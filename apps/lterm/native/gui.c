// lterm app 用到的窗口（macOS）：开一个窗口、收键盘和滚轮、把格子画出来。
// 用纯 C 写：运行的时候 dlopen 打开 AppKit，再通过 Objective-C 的运行时（objc_msgSend）调用它，
// 所以编译时不用 -framework，也不用链接 libobjc（lark.pkg 里只要 c_src 这一行）。不是 macOS 时 lterm_gui_open 返回 -1。
// 格子由 Lark 那边一格一格交过来（码点、前景色、背景色、粗体 / 下划线 / 宽字符），颜色已经算好（0xRRGGBB）。
// 只重画变了的行（lterm_gui_cell 记下哪几行变了，drawRect 只画要重画的那一块）；NSColor 和写字的属性造过的留着不再造。
// 输入法（中文、日文、带声调的字母）：视图实现 NSTextInputClient，按键先交给输入法（interpretKeyEvents:），
// 输入法交回来的字（insertText:）交给 shell，正在拼的字（setMarkedText:）画在光标那里、带下划线，候选框跟着光标（firstRectForCharacterRange:）。
// 鼠标：按下、拖、松开、移动（左、中、右键，带修饰键）排成一队交给 Lark（选中在 vt/sel，交给程序在 vt/mouse）；⌘C 时 Lark 把选中的字放进剪贴板；⌘+ / ⌘- / ⌘0 改字号；标题由 Lark 设。
// 拖窗口边框改大小由这里自己做（不进 AppKit 的循环），所以拖的时候里面跟着改、跟着重画（见 resize_ev）。
// 没做：菜单栏；Option 不当 Meta。
#define _GNU_SOURCE
#include <dlfcn.h>
#include <math.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef void* id;
typedef void* SEL;
typedef void* Class;
#if defined(__arm64__) || defined(__aarch64__)
typedef bool OBool;
#else
typedef signed char OBool;
#endif
typedef struct { double x, y; } LPt;
typedef struct { double w, h; } LSz;
typedef struct { LPt o; LSz s; } LRect;

static void* msg;       // objc_msgSend
static void* msg_st;    // objc_msgSend_stret（只有 x86_64 要：返回 NSRect 这种大的结构）
static SEL (*sel_)(const char*);
static Class (*cls_)(const char*);
static Class (*alloc_cls)(Class, const char*, size_t);
static void (*reg_cls)(Class);
static OBool (*add_m)(Class, SEL, void*, const char*);
static void* (*pool_push)(void);
static void (*pool_pop)(void*);
static void* (*get_proto)(const char*);
static OBool (*add_proto)(Class, void*);

// 按签名把 objc_msgSend 转成对的函数指针（arm64 上不能当可变参数调用）
#define MSG(ret, ...) ((ret (*)(id, SEL, ##__VA_ARGS__))msg)
#define S(name) sel_(name)
#define C(name) ((id)cls_(name))

static id app, win, view, font, bold, fattr, cattr, mode_key;
static double cw = 8, ch = 16, asc = 12;
static const double PAD = 4;
static int R = 0, K = 0;              // 格子的行数、列数
static int* g_cp;                     // 码点（0 是空、-1 是宽字符的右半）
static int* g_fg;
static int* g_bg;
static int* g_fl;                     // 1 粗体、2 下划线、4 宽字符、8 删除线
static int cur_x, cur_y, cur_show;
static int bg0 = 0x1E1E1E, fg0 = 0xD4D4D4;
static int closed;
static int ckm, paste;
static double wheel;
static char* kb;                      // 攒着的按键字节
static size_t kn, kcap;
static char* kout;
// 输入法
typedef struct { unsigned long loc, len; } LRange;
static const unsigned long NOT_FOUND = 0x7FFFFFFFFFFFFFFFUL;   // NSNotFound
static char* marked;                  // 正在拼的字（UTF-8），没有时是 NULL
static unsigned long marked16;        // 它的长度（UTF-16，markedRange 用）
static int inserted;                  // 这次按键输入法交回了字
static int need_show;                 // 正在拼的字变了，要重画

static void kput(const char* s, size_t n) {
  if (kn + n + 1 > kcap) {
    kcap = (kn + n + 1) * 2;
    kb = realloc(kb, kcap);
  }
  memcpy(kb + kn, s, n);
  kn += n;
  kb[kn] = 0;
}

static void kputs_(const char* s) { kput(s, strlen(s)); }

static id nsstr(const char* s) { return MSG(id, const char*)(C("NSString"), S("stringWithUTF8String:"), s); }

// 颜色：造过的留着（256 格的缓存，按颜色值散开），画一格不用每次都造一个 NSColor
static id c_obj[256];
static int c_key[256];
static int hash8(int v) { return (int)(((unsigned)v * 2654435761u) >> 24); }

static id color(int v) {
  int h = hash8(v);
  if (c_obj[h] != NULL && c_key[h] == v) return c_obj[h];
  id o = MSG(id, double, double, double, double)(C("NSColor"), S("colorWithSRGBRed:green:blue:alpha:"),
                                                 ((v >> 16) & 255) / 255.0, ((v >> 8) & 255) / 255.0, (v & 255) / 255.0, 1.0);
  MSG(id)(o, S("retain"));
  if (c_obj[h] != NULL) MSG(void)(c_obj[h], S("release"));
  c_obj[h] = o;
  c_key[h] = v;
  return o;
}

static void fill(int v, double x, double y, double w, double h) {
  MSG(void)(color(v), S("set"));
  LRect r = {{x, y}, {w, h}};
  MSG(void, LRect)(C("NSBezierPath"), S("fillRect:"), r);
}

static LRect bounds_of(id v) {
#if defined(__x86_64__)
  return ((LRect(*)(id, SEL))msg_st)(v, S("bounds"));
#else
  return ((LRect(*)(id, SEL))msg)(v, S("bounds"));
#endif
}

static LRect frame_of(id v) {
#if defined(__x86_64__)
  return ((LRect(*)(id, SEL))msg_st)(v, S("frame"));
#else
  return ((LRect(*)(id, SEL))msg)(v, S("frame"));
#endif
}

static int utf8(int c, char* o) {
  if (c < 0x80) { o[0] = (char)c; o[1] = 0; return 1; }
  if (c < 0x800) { o[0] = (char)(0xC0 | (c >> 6)); o[1] = (char)(0x80 | (c & 63)); o[2] = 0; return 2; }
  if (c < 0x10000) {
    o[0] = (char)(0xE0 | (c >> 12)); o[1] = (char)(0x80 | ((c >> 6) & 63)); o[2] = (char)(0x80 | (c & 63)); o[3] = 0;
    return 3;
  }
  o[0] = (char)(0xF0 | (c >> 18)); o[1] = (char)(0x80 | ((c >> 12) & 63));
  o[2] = (char)(0x80 | ((c >> 6) & 63)); o[3] = (char)(0x80 | (c & 63)); o[4] = 0;
  return 4;
}

// 写字用的属性（字体、颜色）：造过的留着（256 格的缓存）；换了字号（font_gen 变了）时重新造
static int font_gen;
static id a_obj[256];
static int a_key[256];
static int a_gen[256];
static id attrs(int fg, int b) {
  int k = (fg & 0xFFFFFF) | (b ? 1 << 24 : 0);
  int h = hash8(k);
  if (a_obj[h] != NULL && a_key[h] == k && a_gen[h] == font_gen) return a_obj[h];
  id keys[2] = {fattr, cattr};
  id vals[2] = {b ? bold : font, color(fg)};
  id nd = MSG(id, id*, id*, unsigned long)(C("NSDictionary"), S("dictionaryWithObjects:forKeys:count:"), vals, keys, 2);
  MSG(id)(nd, S("retain"));
  if (a_obj[h] != NULL) MSG(void)(a_obj[h], S("release"));
  a_obj[h] = nd;
  a_key[h] = k;
  a_gen[h] = font_gen;
  return nd;
}

// 字号：Menlo（没有时用系统的等宽字体），量一个 M 得到一格的大小
static double font_size;
static void set_font(double size) {
  if (size < 6) size = 6;
  if (size > 72) size = 72;
  font_size = size;
  if (font != NULL) MSG(void)(font, S("release"));
  if (bold != NULL && bold != font) MSG(void)(bold, S("release"));
  font = MSG(id, id, double)(C("NSFont"), S("fontWithName:size:"), nsstr("Menlo"), size);
  if (font == NULL) font = MSG(id, double)(C("NSFont"), S("userFixedPitchFontOfSize:"), size);
  bold = MSG(id, id, double)(C("NSFont"), S("fontWithName:size:"), nsstr("Menlo-Bold"), size);
  if (bold == NULL) bold = font;
  MSG(id)(font, S("retain"));
  if (bold != font) MSG(id)(bold, S("retain"));
  id keys[1] = {fattr};
  id vals[1] = {font};
  id d = MSG(id, id*, id*, unsigned long)(C("NSDictionary"), S("dictionaryWithObjects:forKeys:count:"), vals, keys, 1);
  LSz m = MSG(LSz, id)(nsstr("M"), S("sizeWithAttributes:"), d);
  if (m.w > 0) cw = m.w;
  if (m.h > 0) ch = ceil(m.h);
  asc = ceil(MSG(double)(font, S("ascender")));
  font_gen++;
  if (win != NULL) {
    LSz inc = {cw, ch};
    MSG(void, LSz)(win, S("setContentResizeIncrements:"), inc);
  }
}

// ---------- 鼠标：按下、拖、松开、移动排成一队，Lark 那边一个一个取 ----------

// 一个事件：kind（1 按下、2 拖、3 松开、4 不按键移动）| 点了几下 << 4 | 键 << 8（0 左、1 中、2 右，和 xterm 一样）
//   | 修饰键 << 10（1 Shift、2 Option、4 Ctrl）| 列 << 16 | 行 << 32
static int64_t mq[256];
static int mq_n;
static int copy_req;
// 滚轮在哪一格、按着什么修饰键（Lark 把滚轮交给程序时用）
static int wheel_x, wheel_y, wheel_mods;

static void cell_of(id ev, int* x, int* y) {
  LPt w = MSG(LPt)(ev, S("locationInWindow"));
  LPt p = MSG(LPt, LPt, id)(view, S("convertPoint:fromView:"), w, NULL);
  *x = (int)floor((p.x - PAD) / cw);
  *y = (int)floor((p.y - PAD) / ch);
  if (*x < 0) *x = 0;
  if (*y < 0) *y = 0;
  if (K > 0 && *x >= K) *x = K - 1;
  if (R > 0 && *y >= R) *y = R - 1;
}

static int mods_of(id ev) {
  unsigned long f = MSG(unsigned long)(ev, S("modifierFlags"));
  return ((f & (1UL << 17)) ? 1 : 0) | ((f & (1UL << 19)) ? 2 : 0) | ((f & (1UL << 18)) ? 4 : 0);
}

static void mouse_ev(id ev, int kind) {
  int x, y;
  cell_of(ev, &x, &y);
  long n = kind == 4 ? 0 : MSG(long)(ev, S("clickCount"));
  if (n > 15) n = 15;
  if (n < 0) n = 0;
  // NSEvent 的 buttonNumber：0 左、1 右、2 中；xterm 的是 0 左、1 中、2 右
  long b = kind == 4 ? 0 : MSG(long)(ev, S("buttonNumber"));
  int btn = b == 1 ? 2 : b == 2 ? 1 : 0;
  int64_t v = kind | (int64_t)n << 4 | (int64_t)btn << 8 | (int64_t)mods_of(ev) << 10 | (int64_t)(x & 0xFFFF) << 16 | (int64_t)(y & 0xFFFF) << 32;
  // 连着拖、连着移动只留最新的一个
  if ((kind == 2 || kind == 4) && mq_n > 0 && (mq[mq_n - 1] & 15) == kind) {
    mq[mq_n - 1] = v;
    return;
  }
  if (mq_n < 256) mq[mq_n++] = v;
}

static void mouse_down(id self, SEL c, id ev) { (void)self; (void)c; mouse_ev(ev, 1); }
static void mouse_drag(id self, SEL c, id ev) { (void)self; (void)c; mouse_ev(ev, 2); }
static void mouse_up(id self, SEL c, id ev) { (void)self; (void)c; mouse_ev(ev, 3); }
static void mouse_move(id self, SEL c, id ev) { (void)self; (void)c; mouse_ev(ev, 4); }

// ---------- 视图（运行时造的 NSView 子类） ----------

static OBool yes(id self, SEL c) { (void)self; (void)c; return 1; }

// 只画要重画的那一块（dirty）里的行：lterm_gui_show 只把变了的行标成要重画
static void draw_rect(id self, SEL c, LRect dirty) {
  (void)self; (void)c;
  fill(bg0, dirty.o.x, dirty.o.y, dirty.s.w, dirty.s.h);
  int y0 = (int)floor((dirty.o.y - PAD) / ch);
  int y1 = (int)ceil((dirty.o.y + dirty.s.h - PAD) / ch);
  if (y0 < 0) y0 = 0;
  if (y1 > R) y1 = R;
  for (int y = y0; y < y1; y++) {
    for (int x = 0; x < K; x++) {
      int i = y * K + x;
      int cp = g_cp[i];
      if (cp == -1) continue;
      int fg = g_fg[i], bg = g_bg[i], fl = g_fl[i];
      double w = (fl & 4) ? 2 * cw : cw;
      double px = PAD + x * cw, py = PAD + y * ch;
      if (cur_show && x == cur_x && y == cur_y) {
        int t = fg; fg = bg; bg = t;
      }
      if (bg != bg0) fill(bg, px, py, w, ch);
      if (cp > 32 && fg != bg) {
        char u[8];
        utf8(cp, u);
        LPt p = {px, py};
        MSG(void, LPt, id)(nsstr(u), S("drawAtPoint:withAttributes:"), p, attrs(fg, fl & 1));
      }
      if (fl & 2) fill(fg, px, py + asc + 1, w, 1);
      if (fl & 8) fill(fg, px, py + ch / 2, w, 1);
    }
  }
  // 正在拼的字：盖在光标那里，带下划线
  if (marked != NULL && marked[0] != 0) {
    id t = nsstr(marked);
    id a = attrs(fg0, 0);
    LSz z = MSG(LSz, id)(t, S("sizeWithAttributes:"), a);
    double px = PAD + cur_x * cw, py = PAD + cur_y * ch;
    fill(bg0, px, py, z.w, ch);
    LPt p = {px, py};
    MSG(void, LPt, id)(t, S("drawAtPoint:withAttributes:"), p, a);
    fill(fg0, px, py + asc + 1, z.w, 1);
  }
}

static const char* fkey(int k) {
  switch (k) {
    case 0xF700: return ckm ? "\x1bOA" : "\x1b[A";
    case 0xF701: return ckm ? "\x1bOB" : "\x1b[B";
    case 0xF702: return ckm ? "\x1bOD" : "\x1b[D";
    case 0xF703: return ckm ? "\x1bOC" : "\x1b[C";
    case 0xF704: return "\x1bOP";
    case 0xF705: return "\x1bOQ";
    case 0xF706: return "\x1bOR";
    case 0xF707: return "\x1bOS";
    case 0xF708: return "\x1b[15~";
    case 0xF709: return "\x1b[17~";
    case 0xF70A: return "\x1b[18~";
    case 0xF70B: return "\x1b[19~";
    case 0xF70C: return "\x1b[20~";
    case 0xF70D: return "\x1b[21~";
    case 0xF70E: return "\x1b[23~";
    case 0xF70F: return "\x1b[24~";
    case 0xF727: return "\x1b[2~";
    case 0xF728: return "\x1b[3~";
    case 0xF729: return ckm ? "\x1bOH" : "\x1b[H";
    case 0xF72B: return ckm ? "\x1bOF" : "\x1b[F";
    case 0xF72C: return "\x1b[5~";
    case 0xF72D: return "\x1b[6~";
  }
  return "";
}

static void key_down(id self, SEL c, id ev) {
  (void)self; (void)c;
  unsigned long mods = MSG(unsigned long)(ev, S("modifierFlags"));
  id s = MSG(id)(ev, S("characters"));
  id raw = MSG(id)(ev, S("charactersIgnoringModifiers"));
  unsigned long n = MSG(unsigned long)(s, S("length"));
  int k0 = 0;
  if (MSG(unsigned long)(raw, S("length")) > 0) k0 = MSG(unsigned short, unsigned long)(raw, S("characterAtIndex:"), 0);
  // Command：⌘V 粘贴、⌘C 复制（Lark 那边取选中的字）、⌘+ / ⌘- / ⌘0 改字号、⌘Q / ⌘W 关窗口，别的不管
  if (mods & (1UL << 20)) {
    if (k0 == 'q' || k0 == 'w') closed = 1;
    if (k0 == 'c') copy_req = 1;
    if (k0 == '=' || k0 == '+') set_font(font_size + 1);
    if (k0 == '-') set_font(font_size - 1);
    if (k0 == '0') set_font(14);
    if (k0 == '=' || k0 == '+' || k0 == '-' || k0 == '0') need_show = 1;
    if (k0 == 'v') {
      id pb = MSG(id)(C("NSPasteboard"), S("generalPasteboard"));
      id t = MSG(id, id)(pb, S("stringForType:"), nsstr("public.utf8-plain-text"));
      if (t != NULL) {
        const char* u = MSG(const char*)(t, S("UTF8String"));
        if (paste) kputs_("\x1b[200~");
        // 换行按回车交过去（别的终端也这样）
        for (const char* p = u; p != NULL && *p; p++) kput(*p == 0x0A ? "\r" : p, 1);
        if (paste) kputs_("\x1b[201~");
      }
    }
    return;
  }
  // 先交给输入法：它交回字（insertText:）就用它的；正在拼字（前后有一个时候在拼）时按键归输入法；
  // 都没有时（回车、退格、方向键、Ctrl-字母，输入法只调 doCommandBySelector:）按下面原来的样子发
  int was = marked != NULL && marked[0] != 0;
  inserted = 0;
  MSG(void, id)(view, S("interpretKeyEvents:"), MSG(id, id)(C("NSArray"), S("arrayWithObject:"), ev));
  int now = marked != NULL && marked[0] != 0;
  if (inserted || was || now) return;
  if (n == 0) return;
  int k = MSG(unsigned short, unsigned long)(s, S("characterAtIndex:"), 0);
  if (n == 1 && k >= 0xF700 && k <= 0xF8FF) {
    kputs_(fkey(k));
    return;
  }
  // Shift-Tab
  if (n == 1 && k == 0x19) {
    kputs_("\x1b[Z");
    return;
  }
  const char* u = MSG(const char*)(s, S("UTF8String"));
  if (u != NULL) kputs_(u);
}

// ---------- 输入法（NSTextInputClient） ----------

// 输入法给的可能是 NSString，也可能是 NSAttributedString
static id plain(id s) {
  if (s != NULL && MSG(OBool, id)(s, S("isKindOfClass:"), C("NSAttributedString"))) return MSG(id)(s, S("string"));
  return s;
}

static void set_marked(id s) {
  free(marked);
  marked = NULL;
  marked16 = 0;
  if (s != NULL) {
    const char* u = MSG(const char*)(s, S("UTF8String"));
    if (u != NULL && u[0] != 0) marked = strdup(u);
    marked16 = MSG(unsigned long)(s, S("length"));
  }
  need_show = 1;
}

static void insert_text(id self, SEL c, id s, LRange r) {
  (void)self; (void)c; (void)r;
  id t = plain(s);
  const char* u = t != NULL ? MSG(const char*)(t, S("UTF8String")) : NULL;
  if (u != NULL) kputs_(u);
  set_marked(NULL);
  inserted = 1;
}

static void set_marked_text(id self, SEL c, id s, LRange sel, LRange r) {
  (void)self; (void)c; (void)sel; (void)r;
  set_marked(plain(s));
}

static void unmark_text(id self, SEL c) {
  (void)self; (void)c;
  set_marked(NULL);
}

static OBool has_marked(id self, SEL c) {
  (void)self; (void)c;
  return marked != NULL;
}

static LRange marked_range(id self, SEL c) {
  (void)self; (void)c;
  LRange r = {NOT_FOUND, 0};
  if (marked != NULL) r.loc = 0, r.len = marked16;
  return r;
}

static LRange selected_range(id self, SEL c) {
  (void)self; (void)c;
  LRange r = {NOT_FOUND, 0};
  return r;
}

static id valid_attrs(id self, SEL c) {
  (void)self; (void)c;
  return MSG(id)(C("NSArray"), S("array"));
}

static id attributed_sub(id self, SEL c, LRange r, LRange* actual) {
  (void)self; (void)c; (void)r; (void)actual;
  return NULL;
}

static unsigned long char_index(id self, SEL c, LPt p) {
  (void)self; (void)c; (void)p;
  return NOT_FOUND;
}

// 候选框放在光标下面：光标那一格换成屏幕上的坐标
static LRect first_rect(id self, SEL c, LRange r, LRange* actual) {
  (void)self; (void)c; (void)r;
  if (actual != NULL) actual->loc = NOT_FOUND, actual->len = 0;
  LRect v = {{PAD + cur_x * cw, PAD + cur_y * ch}, {cw, ch}};
#if defined(__x86_64__)
  LRect w = ((LRect(*)(id, SEL, LRect, id))msg_st)(view, S("convertRect:toView:"), v, NULL);
  return ((LRect(*)(id, SEL, LRect))msg_st)(win, S("convertRectToScreen:"), w);
#else
  LRect w = ((LRect(*)(id, SEL, LRect, id))msg)(view, S("convertRect:toView:"), v, NULL);
  return ((LRect(*)(id, SEL, LRect))msg)(win, S("convertRectToScreen:"), w);
#endif
}

// 回车、退格这些：输入法不处理时调它，什么都不做（keyDown: 里按原来的样子发）
static void do_command(id self, SEL c, SEL cmd) { (void)self; (void)c; (void)cmd; }

static void scroll_wheel(id self, SEL c, id ev) {
  (void)self; (void)c;
  double d = MSG(double)(ev, S("scrollingDeltaY"));
  OBool precise = MSG(OBool)(ev, S("hasPreciseScrollingDeltas"));
  wheel += precise ? d / ch : d;
  cell_of(ev, &wheel_x, &wheel_y);
  wheel_mods = mods_of(ev);
}

// ---------- 给 Lark 用的 ----------

// LTERM_DEBUG=1 时一步一步写到标准错误（窗口出不来时看卡在哪一步）
static void dbg(const char* s) {
  if (getenv("LTERM_DEBUG") != NULL) fprintf(stderr, "lterm gui：%s\n", s);
}

// 开窗口：rows × cols 个格子，字号 size；成功返回 0，失败返回负的步骤号（-1 打不开 AppKit、-2 找不到运行时的函数、-3 找不到类、-4 造不出窗口）
int lterm_gui_open(int rows, int cols, int size) {
  dbg("打开 AppKit");
  void* h = dlopen("/System/Library/Frameworks/AppKit.framework/AppKit", RTLD_NOW | RTLD_GLOBAL);
  if (h == NULL) {
    dbg(dlerror());
    return -1;
  }
  msg = dlsym(RTLD_DEFAULT, "objc_msgSend");
  msg_st = dlsym(RTLD_DEFAULT, "objc_msgSend_stret");
  sel_ = (SEL(*)(const char*))dlsym(RTLD_DEFAULT, "sel_registerName");
  cls_ = (Class(*)(const char*))dlsym(RTLD_DEFAULT, "objc_getClass");
  alloc_cls = (Class(*)(Class, const char*, size_t))dlsym(RTLD_DEFAULT, "objc_allocateClassPair");
  reg_cls = (void (*)(Class))dlsym(RTLD_DEFAULT, "objc_registerClassPair");
  add_m = (OBool(*)(Class, SEL, void*, const char*))dlsym(RTLD_DEFAULT, "class_addMethod");
  pool_push = (void* (*)(void))dlsym(RTLD_DEFAULT, "objc_autoreleasePoolPush");
  pool_pop = (void (*)(void*))dlsym(RTLD_DEFAULT, "objc_autoreleasePoolPop");
  get_proto = (void* (*)(const char*))dlsym(RTLD_DEFAULT, "objc_getProtocol");
  add_proto = (OBool(*)(Class, void*))dlsym(RTLD_DEFAULT, "class_addProtocol");
  id* fa = (id*)dlsym(RTLD_DEFAULT, "NSFontAttributeName");
  id* ca = (id*)dlsym(RTLD_DEFAULT, "NSForegroundColorAttributeName");
  id* md = (id*)dlsym(RTLD_DEFAULT, "NSDefaultRunLoopMode");
  if (!msg || !sel_ || !cls_ || !alloc_cls || !reg_cls || !add_m || !pool_push || !pool_pop || !get_proto || !add_proto || !fa || !ca || !md) return -2;
#if defined(__x86_64__)
  if (!msg_st) return -2;
#endif
  fattr = *fa;
  cattr = *ca;
  mode_key = *md;
  void* pool = pool_push();
  if (cls_("NSApplication") == NULL || cls_("NSWindow") == NULL || cls_("NSView") == NULL) {
    pool_pop(pool);
    return -3;
  }
  dbg("NSApplication");
  app = MSG(id)(C("NSApplication"), S("sharedApplication"));
  MSG(OBool, long)(app, S("setActivationPolicy:"), 0);
  MSG(void)(app, S("finishLaunching"));

  dbg("字体");
  set_font((double)size);

  dbg("视图的类");
  Class vc = cls_("LtermView");
  if (vc == NULL) {
    vc = alloc_cls(cls_("NSView"), "LtermView", 0);
    add_m(vc, S("isFlipped"), (void*)yes, "c@:");
    add_m(vc, S("acceptsFirstResponder"), (void*)yes, "c@:");
    add_m(vc, S("drawRect:"), (void*)draw_rect, "v@:{CGRect={CGPoint=dd}{CGSize=dd}}");
    add_m(vc, S("keyDown:"), (void*)key_down, "v@:@");
    add_m(vc, S("scrollWheel:"), (void*)scroll_wheel, "v@:@");
    add_m(vc, S("mouseDown:"), (void*)mouse_down, "v@:@");
    add_m(vc, S("mouseDragged:"), (void*)mouse_drag, "v@:@");
    add_m(vc, S("mouseUp:"), (void*)mouse_up, "v@:@");
    add_m(vc, S("rightMouseDown:"), (void*)mouse_down, "v@:@");
    add_m(vc, S("rightMouseDragged:"), (void*)mouse_drag, "v@:@");
    add_m(vc, S("rightMouseUp:"), (void*)mouse_up, "v@:@");
    add_m(vc, S("otherMouseDown:"), (void*)mouse_down, "v@:@");
    add_m(vc, S("otherMouseDragged:"), (void*)mouse_drag, "v@:@");
    add_m(vc, S("otherMouseUp:"), (void*)mouse_up, "v@:@");
    add_m(vc, S("mouseMoved:"), (void*)mouse_move, "v@:@");
    // 输入法：NSTextInputClient 的方法，再声明遵守这个协议（不遵守时 NSView 不给输入法的上下文）
    const char* rg = "{_NSRange=QQ}";
    char t[128];
    snprintf(t, sizeof t, "v@:@%s", rg);
    add_m(vc, S("insertText:replacementRange:"), (void*)insert_text, t);
    snprintf(t, sizeof t, "v@:@%s%s", rg, rg);
    add_m(vc, S("setMarkedText:selectedRange:replacementRange:"), (void*)set_marked_text, t);
    add_m(vc, S("unmarkText"), (void*)unmark_text, "v@:");
    add_m(vc, S("hasMarkedText"), (void*)has_marked, "c@:");
    snprintf(t, sizeof t, "%s@:", rg);
    add_m(vc, S("markedRange"), (void*)marked_range, t);
    add_m(vc, S("selectedRange"), (void*)selected_range, t);
    add_m(vc, S("validAttributesForMarkedText"), (void*)valid_attrs, "@@:");
    snprintf(t, sizeof t, "@@:%s^%s", rg, rg);
    add_m(vc, S("attributedSubstringForProposedRange:actualRange:"), (void*)attributed_sub, t);
    add_m(vc, S("characterIndexForPoint:"), (void*)char_index, "Q@:{CGPoint=dd}");
    snprintf(t, sizeof t, "{CGRect={CGPoint=dd}{CGSize=dd}}@:%s^%s", rg, rg);
    add_m(vc, S("firstRectForCharacterRange:actualRange:"), (void*)first_rect, t);
    add_m(vc, S("doCommandBySelector:"), (void*)do_command, "v@::");
    void* proto = get_proto("NSTextInputClient");
    if (proto != NULL) {
      add_proto(vc, proto);
    } else {
      dbg("找不到 NSTextInputClient 协议：输入法用不了");
    }
    reg_cls(vc);
  }
  LRect r = {{0, 0}, {cols * cw + 2 * PAD, rows * ch + 2 * PAD}};
  dbg("窗口");
  win = MSG(id)(C("NSWindow"), S("alloc"));
  // 有标题、能关、能最小化、能改大小；NSBackingStoreBuffered
  win = MSG(id, LRect, unsigned long, unsigned long, OBool)(win, S("initWithContentRect:styleMask:backing:defer:"), r, 15, 2, 0);
  if (win == NULL) {
    pool_pop(pool);
    return -4;
  }
  MSG(void, OBool)(win, S("setReleasedWhenClosed:"), 0);
  // 不按键移动也要收（程序打开 ?1003 时交给它；Lark 那边没打开时扔掉）
  MSG(void, OBool)(win, S("setAcceptsMouseMovedEvents:"), 1);
  MSG(void, id)(win, S("setTitle:"), nsstr("lterm"));
  LSz inc = {cw, ch};
  MSG(void, LSz)(win, S("setContentResizeIncrements:"), inc);
  view = MSG(id)((id)vc, S("alloc"));
  view = MSG(id, LRect)(view, S("initWithFrame:"), r);
  // AppKit 自己改大小的时候（比如绿色按钮放大）也调 drawRect:，不把旧的画面拉伸
  MSG(void, long)(view, S("setLayerContentsRedrawPolicy:"), 2);
  MSG(void, id)(win, S("setContentView:"), view);
  MSG(void)(win, S("center"));
  dbg("显示窗口");
  MSG(void, id)(win, S("makeKeyAndOrderFront:"), NULL);
  // 不是从 .app 启动的程序不一定会到最前面：直接放到最前面，再把程序激活（macOS 14 起用 activate）
  MSG(void)(win, S("orderFrontRegardless"));
  MSG(OBool, id)(win, S("makeFirstResponder:"), view);
  if (MSG(OBool, SEL)(app, S("respondsToSelector:"), S("activate"))) {
    MSG(void)(app, S("activate"));
  } else {
    MSG(void, OBool)(app, S("activateIgnoringOtherApps:"), 1);
  }
  dbg("好了");
  pool_pop(pool);
  return 0;
}

// ---------- 自己改窗口大小 ----------
// 拖窗口边框时 AppKit 会进它自己的循环（sendEvent: 一直到松手才返回），Lark 那边的循环停着，窗口变大了里面不重画。
// 所以在边框上按下时不交给 AppKit，自己跟着鼠标改窗口大小（按格子对齐）：每拖一下 pump 就返回，
// Lark 那边看到大小变了，跟着改屏幕和伪终端，马上重画。全屏时不管。
static const double EDGE = 4;     // 离窗口的边多近算按在边框上（就是格子外面空出来的 PAD，不会抢走选字）
static int rz;                    // 正在拖哪几条边：1 左、2 右、4 下、8 上；0 是没在拖
static LPt rz_m;                  // 按下时鼠标在屏幕上的位置
static LRect rz_f;                // 按下时窗口的位置和大小
static double rz_dw, rz_dh;       // 窗口比里面的内容大多少（标题栏）

static int edge_at(id ev) {
  if (MSG(id)(ev, S("window")) != win) return 0;
  if (MSG(unsigned long)(win, S("styleMask")) & (1UL << 14)) return 0;
  LPt p = MSG(LPt)(ev, S("locationInWindow"));
  LRect f = frame_of(win);
  int e = 0;
  if (p.x < EDGE) e |= 1;
  if (p.x > f.s.w - EDGE) e |= 2;
  if (p.y < EDGE) e |= 4;
  if (p.y > f.s.h - 2) e |= 8;    // 上边只留一点：标题栏要能拖着移动窗口
  return e;
}

// 内容按格子对齐：PAD + n 格 + PAD，至少 min 格
static double snap(double content, double cell, int min) {
  int n = (int)floor((content - 2 * PAD) / cell + 0.5);
  if (n < min) n = min;
  return n * cell + 2 * PAD;
}

static void rz_move(void) {
  LPt m = MSG(LPt)(C("NSEvent"), S("mouseLocation"));
  double dx = m.x - rz_m.x, dy = m.y - rz_m.y;
  double w = rz_f.s.w - rz_dw, h = rz_f.s.h - rz_dh;
  if (rz & 1) w -= dx;
  if (rz & 2) w += dx;
  if (rz & 4) h -= dy;
  if (rz & 8) h += dy;
  LRect f = rz_f;
  f.s.w = snap(w, cw, 10) + rz_dw;
  f.s.h = snap(h, ch, 3) + rz_dh;
  // 屏幕坐标 y 朝上：拖左边时右边不动，拖下边时上边不动
  if (rz & 1) f.o.x = rz_f.o.x + rz_f.s.w - f.s.w;
  if (rz & 4) f.o.y = rz_f.o.y + rz_f.s.h - f.s.h;
  LRect now = frame_of(win);
  if (now.o.x == f.o.x && now.o.y == f.o.y && now.s.w == f.s.w && now.s.h == f.s.h) return;
  MSG(void, LRect, OBool)(win, S("setFrame:display:"), f, 1);
}

// 是改大小的事件就自己处理（返回 1），不是的交给 AppKit
static int resize_ev(id e) {
  unsigned long t = MSG(unsigned long)(e, S("type"));
  if (rz != 0) {
    if (t == 6) {                 // 左键拖
      rz_move();
      return 1;
    }
    if (t == 2) {                 // 左键松开
      rz_move();
      rz = 0;
      return 1;
    }
    return 0;
  }
  if (t != 1) return 0;           // 左键按下
  int ed = edge_at(e);
  if (ed == 0) return 0;
  rz = ed;
  rz_m = MSG(LPt)(C("NSEvent"), S("mouseLocation"));
  rz_f = frame_of(win);
  LRect b = bounds_of(view);
  rz_dw = rz_f.s.w - b.s.w;
  rz_dh = rz_f.s.h - b.s.h;
  return 1;
}

// 处理窗口的事件：最多等 ms 毫秒等第一个，然后把攒着的都处理掉；窗口还开着返回 1
int lterm_gui_pump(int ms) {
  if (app == NULL) return 0;
  void* pool = pool_push();
  id until = MSG(id, double)(C("NSDate"), S("dateWithTimeIntervalSinceNow:"), ms / 1000.0);
  id past = MSG(id)(C("NSDate"), S("distantPast"));
  SEL sig = S("nextEventMatchingMask:untilDate:inMode:dequeue:");
  id e = MSG(id, unsigned long, id, id, OBool)(app, sig, ~0UL, until, mode_key, 1);
  while (e != NULL) {
    if (!resize_ev(e)) MSG(void, id)(app, S("sendEvent:"), e);
    // 拖着边框时每动一下就回到 Lark 那边，让它跟着改大小、重画
    if (rz != 0) break;
    e = MSG(id, unsigned long, id, id, OBool)(app, sig, ~0UL, past, mode_key, 1);
  }
  MSG(void)(app, S("updateWindows"));
  // 正在拼的字变了：Lark 那边不知道，这里自己重画
  if (need_show) {
    need_show = 0;
    MSG(void, OBool)(view, S("setNeedsDisplay:"), 1);
    MSG(void)(view, S("displayIfNeeded"));
  }
  if (!MSG(OBool)(win, S("isVisible"))) {
    dbg("窗口不见了");
    closed = 1;
  }
  pool_pop(pool);
  return closed ? 0 : 1;
}

// 攒着的按键（取走以后清空）
const char* lterm_gui_keys(void) {
  free(kout);
  kout = kb != NULL ? kb : calloc(1, 1);
  kb = NULL;
  kn = 0;
  kcap = 0;
  return kout;
}

// 攒着的滚轮：往上滚是正的，按行算（取走整数部分）
int lterm_gui_scroll(void) {
  int n = (int)wheel;
  wheel -= n;
  return n;
}

// 窗口现在放得下几个格子：行 << 16 | 列
int lterm_gui_size(void) {
  if (view == NULL) return -1;
  LRect b = bounds_of(view);
  int c = (int)((b.s.w - 2 * PAD) / cw + 0.01);
  int r = (int)((b.s.h - 2 * PAD) / ch + 0.01);
  if (c < 1) c = 1;
  if (r < 1) r = 1;
  return r << 16 | c;
}

// 要重画的行：[d_lo, d_hi]（d_lo > d_hi 时没有）；d_all 是整个窗口
static int d_lo = 1, d_hi = 0, d_all = 1;

static void dirty_row(int y) {
  if (y < d_lo) d_lo = y;
  if (y > d_hi) d_hi = y;
}

// 格子改成 rows × cols（清空）
void lterm_gui_grid(int rows, int cols) {
  d_all = 1;
  R = rows;
  K = cols;
  size_t n = (size_t)rows * (size_t)cols;
  g_cp = realloc(g_cp, n * sizeof(int));
  g_fg = realloc(g_fg, n * sizeof(int));
  g_bg = realloc(g_bg, n * sizeof(int));
  g_fl = realloc(g_fl, n * sizeof(int));
  for (size_t i = 0; i < n; i++) {
    g_cp[i] = 0;
    g_fg[i] = fg0;
    g_bg[i] = bg0;
    g_fl[i] = 0;
  }
}

void lterm_gui_cell(int y, int x, int cp, int fg, int bg, int fl) {
  if (y < 0 || y >= R || x < 0 || x >= K) return;
  int i = y * K + x;
  if (g_cp[i] == cp && g_fg[i] == fg && g_bg[i] == bg && g_fl[i] == fl) return;
  g_cp[i] = cp;
  g_fg[i] = fg;
  g_bg[i] = bg;
  g_fl[i] = fl;
  dirty_row(y);
}

// 默认的前景色、背景色（格子外面的边也是背景色）
void lterm_gui_colors(int fg, int bg) {
  fg0 = fg;
  bg0 = bg;
  d_all = 1;
}

void lterm_gui_cursor(int x, int y, int show) {
  if (x == cur_x && y == cur_y && show == cur_show) return;
  dirty_row(cur_y);
  dirty_row(y);
  cur_x = x;
  cur_y = y;
  cur_show = show;
}

// 里面的程序打开的模式：方向键（DECCKM）、括号粘贴
void lterm_gui_modes(int c, int p) {
  ckm = c;
  paste = p;
}

// 画出来：只重画变了的那几行（从最上面变了的一行到最下面变了的一行）
void lterm_gui_show(void) {
  if (view == NULL) return;
  if (!d_all && d_lo > d_hi) return;
  void* pool = pool_push();
  if (d_all) {
    MSG(void, OBool)(view, S("setNeedsDisplay:"), 1);
  } else {
    LRect b = bounds_of(view);
    double top = d_lo == 0 ? 0 : PAD + d_lo * ch;
    double bot = d_hi >= R - 1 ? b.s.h : PAD + (d_hi + 1) * ch;
    LRect r = {{0, top}, {b.s.w, bot - top}};
    MSG(void, LRect)(view, S("setNeedsDisplayInRect:"), r);
  }
  MSG(void)(view, S("displayIfNeeded"));
  d_all = 0;
  d_lo = 1;
  d_hi = 0;
  pool_pop(pool);
}

// 下一个鼠标事件（见 mouse_ev），没有时是 -1
int64_t lterm_gui_mouse(void) {
  if (mq_n == 0) return -1;
  int64_t v = mq[0];
  memmove(mq, mq + 1, (size_t)(mq_n - 1) * sizeof(int64_t));
  mq_n--;
  return v;
}

// 按了 ⌘C 没有（取走以后清掉）
int lterm_gui_copy_req(void) {
  int v = copy_req;
  copy_req = 0;
  return v;
}

// 放进系统的剪贴板
void lterm_gui_clip(const char* s) {
  if (app == NULL || s == NULL) return;
  void* pool = pool_push();
  id pb = MSG(id)(C("NSPasteboard"), S("generalPasteboard"));
  MSG(long)(pb, S("clearContents"));
  MSG(OBool, id, id)(pb, S("setString:forType:"), nsstr(s), nsstr("public.utf8-plain-text"));
  pool_pop(pool);
}

void lterm_gui_title(const char* t) {
  if (win == NULL || t == NULL) return;
  void* pool = pool_push();
  id s = nsstr(t);
  // 不是合法的 UTF-8 时 stringWithUTF8String: 返回 nil
  if (s != NULL) MSG(void, id)(win, S("setTitle:"), s);
  pool_pop(pool);
}

// 滚轮最后在哪一格：行 << 16 | 列；修饰键 << 32
int64_t lterm_gui_wheel_at(void) { return (int64_t)wheel_mods << 32 | (int64_t)(wheel_y & 0xFFFF) << 16 | (wheel_x & 0xFFFF); }
