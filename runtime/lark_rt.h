// Lark0 运行时：字符串、内存、I/O。所有函数都是 static，生成的 C 文件单独编译即可。
//
// 分成两部分。核心：引用计数、字符串、调用栈、整数和浮点数、print / panic / exit、读写整个文件、哈希、时间、测试，
// 只用 C 标准库加上 unistd（_exit；测试的执行器另外用 fork、pipe、waitpid）。可选：std/os 的文件系统、文件描述符、终端、
// 子进程、时区、信号、套接字，以及任务、调度器、事件循环、定时器、栈溢出保护、Mutex、Chan。
// 定义了 LK_CORE 时只带核心：没有别的线程，不用 pthread，锁和 pthread_once 换成普通的写法。程序没有 import 系统层的
// std 模块、也没有用到任务、通道、锁和系统的内置函数时，编译器在生成的 C 开头定义它；编译 C 时加 -DLK_FULL 可以强制带上全部。
// 再定义 LK_BARE（没有操作系统）时，核心也不直接用 stdio、exit、时钟和系统随机数：都经过下面“平台”一节的五个 lark_plat_* 函数，
// 由使用者提供（例子见 examples/bare）；读写文件、system 在运行时 panic，测试的执行器没有。
#ifndef LARK_RT_H
#define LARK_RT_H

// 没有操作系统（LK_BARE）只能用于只带核心的程序：生成的 C 在包含这个文件之前定义 LK_CORE
#if defined(LK_BARE) && !defined(LK_CORE)
#error "LK_BARE 只能用于只带运行时核心的程序：不 import 系统层的模块，不用任务、通道、锁和系统的内置函数（也不要加 -DLK_FULL）"
#endif

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <errno.h>
#include <math.h>
#ifndef LK_BARE
#include <time.h>
#include <unistd.h>
#include <sys/wait.h>
#endif
#ifndef LK_CORE
#include <pthread.h>
#include <dirent.h>
#include <fcntl.h>
#include <sys/socket.h>
#include <netdb.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/stat.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <poll.h>
#endif

// 移走：按位复制后把原变量清零（析构函数对零值什么都不做）
#define LK_MOVE(x) ({ __typeof__(x) lk_mv_ = (x); memset(&(x), 0, sizeof(x)); lk_mv_; })

// ---------- 平台：输出、退出、时间、随机数 ----------
// 核心只通过下面五个函数和外界打交道（另外用到 C 库里不碰系统的部分：内存、字符串、snprintf、strtod、数学函数）。
// 平常用 C 库和系统调用实现；定义了 LK_BARE（没有操作系统，见 examples/bare）时由使用者用 C 提供：
//   lark_plat_write(fd, p, n)  把 n 个字节写出去：fd 1 是 print，2 是 eprint 和 panic 的信息
//   lark_plat_exit(code)       结束程序（exit、panic、main 返回以后不会再调用），不返回
//   lark_plat_now_ns()         墙上时间，1970 年起的纳秒数（now_ms、time.unix_ms 用；没有时钟可以返回 0）
//   lark_plat_mono_ns()        单调时钟的纳秒数，只用来量间隔（time.now、time.elapsed_ms 用）
//   lark_plat_random(p, n)     填满 n 个随机字节：字符串哈希的密钥（没有硬件随机数时用别的办法凑，比如计时器的值）
// LK_BARE 时读写文件、system 都在运行时 panic（编译能过，因为它们是核心里的内置函数）
#ifdef LK_BARE
void lark_plat_write(int fd, const char* p, size_t n);
void lark_plat_exit(int code) __attribute__((noreturn));
int64_t lark_plat_now_ns(void);
int64_t lark_plat_mono_ns(void);
void lark_plat_random(void* p, size_t n);
#define lk_flush_out() ((void)0)
#else
// stdout 有缓冲、stderr 没有：panic 前先把 stdout 写出去（lk_flush_out），两路输出合在一起看时顺序才对。
// eprint 不先写 stdout：和 C 程序平常的行为一样
static void __attribute__((unused)) lark_plat_write(int fd, const char* p, size_t n) {
  if (n > 0) fwrite(p, 1, n, fd == 2 ? stderr : stdout);
}
#define lk_flush_out() fflush(stdout)

static void __attribute__((unused)) lark_plat_random(void* p, size_t n) {
#if defined(__APPLE__) || defined(__FreeBSD__) || defined(__OpenBSD__) || defined(__NetBSD__)
  arc4random_buf(p, n);
#else
  if (getentropy(p, n) != 0) {
    // 取不到系统随机数时退而求其次：时间、进程号和栈地址
    uint64_t k[2] = {(uint64_t)time(NULL) ^ ((uint64_t)getpid() << 32), (uint64_t)(uintptr_t)&k ^ (uint64_t)clock()};
    memcpy(p, k, n < sizeof k ? n : sizeof k);
  }
#endif
}

static int64_t __attribute__((unused)) lark_plat_now_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_REALTIME, &ts);
  return (int64_t)ts.tv_sec * 1000000000 + ts.tv_nsec;
}

static int64_t __attribute__((unused)) lark_plat_mono_ns(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (int64_t)ts.tv_sec * 1000000000 + ts.tv_nsec;
}
#endif

static void __attribute__((unused)) lk_write_c(int fd, const char* s) { lark_plat_write(fd, s, strlen(s)); }

// 格式化后写到标准错误（panic 和调用栈用）：先在栈上的缓冲里排好，再整段写出，太长时截断
static void lk_errf(const char* fmt, ...) __attribute__((format(printf, 1, 2), unused));
static void lk_errf(const char* fmt, ...) {
  char buf[512];
  va_list ap;
  va_start(ap, fmt);
  int n = vsnprintf(buf, sizeof buf, fmt, ap);
  va_end(ap);
  if (n < 0) return;
  lark_plat_write(2, buf, (size_t)n < sizeof buf ? (size_t)n : sizeof buf - 1);
}

// ---------- 调用栈：panic 时指回 .lark 源码 ----------
// lark1 生成的每个函数（和闭包）开头都有一个 LK_FRAME：记下函数名、文件和当前行，挂在本线程的链表上，
// 函数返回时（任何一个 return）由 cleanup 自动摘下；可能 panic 或调用函数的语句之前用 LK_LINE 更新行号（见编译器的 quiet_stmt）。panic 时从里到外打印。
// 编译 C 时加 -DLK_NOTRACE 可以关掉：这两个宏什么都不做，panic 时不打印调用栈（省掉每次调用和每条语句的开销）。
// -DLK_NOLINE 只关掉行号：仍然记每一层的函数，panic 时打印的行号是函数开头那一行。用来分开量两部分的开销（make bench）。
#ifdef LK_NOTRACE
#define LK_FRAME(fn_, file_, line_) ((void)0)
#define LK_LINE(n_) ((void)0)
static void lk_trace(void) {}
#else
typedef struct lk_frame {
  const char* fn;
  const char* file;
  int line;
  struct lk_frame* prev;
  struct lk_frame** slot;   // 这一帧挂在哪个栈顶上，摘下时用
} lk_frame;

// 每个任务一条链（见文件末尾的“任务与调度器”）。macOS 上访问 __thread 变量要经过一次函数调用（tlv_get_addr），
// 每次调用都付这笔开销太贵，所以没有别的任务时（lk_nthreads 为 0，见下面的 lk_rc_inc）直接用普通全局变量 lk_main_top：
// 这时只有主任务在运行。有别的任务时，工作线程每换上一个任务，就把本线程的 lk_slot_ 指向这个任务的链头。
// 帧里记的 slot 指向任务自己的链头，任务换到别的线程上继续运行时也不会变。
static lk_frame* lk_main_top;
#ifndef LK_CORE
static __thread lk_frame* lk_top_;
static __thread lk_frame** lk_slot_;
#endif
static inline lk_frame** lk_slot(void);

static void __attribute__((unused)) lk_frame_pop(lk_frame* f) { *f->slot = f->prev; }

#define LK_FRAME(fn_, file_, line_) \
  lk_frame** lk_sl = lk_slot(); \
  __attribute__((cleanup(lk_frame_pop))) lk_frame lk_fr = { (fn_), (file_), (line_), *lk_sl, lk_sl }; \
  *lk_sl = &lk_fr
#ifdef LK_NOLINE
#define LK_LINE(n_) ((void)0)
#else
#define LK_LINE(n_) (lk_fr.line = (n_))
#endif

static void lk_trace(void) {
  int n = 0;
  for (lk_frame* f = *lk_slot(); f; f = f->prev) {
    if (n == 20) {
      int rest = 0;
      for (; f; f = f->prev) rest++;
      lk_errf("  …（还有 %d 层）\n", rest);
      break;
    }
    lk_errf("  在 %s（%s:%d）\n", f->fn, f->file, f->line);
    n++;
  }
}
#endif

// 退出钩子（os.at_exit，见 lark_at_exit）正在跑时为 1：这时再 exit 或 panic 就直接 _exit，剩下的钩子不再跑
// （C 不允许在 atexit 的处理函数里再调 exit）
#ifndef LK_BARE
static volatile int lk_exiting = 0;
#endif
static void __attribute__((noreturn, unused)) lk_die(int code) {
#ifdef LK_BARE
  lark_plat_exit(code);
#else
  if (lk_exiting) _exit(code);
  exit(code);
#endif
}

static void lk_panic_c(const char* msg) __attribute__((noreturn, unused));
static void lk_panic_c(const char* msg) {
  lk_flush_out();       // 先把已经 print 的内容写出去，两路输出合在一起看时顺序才对
  lk_write_c(2, "panic: ");
  lk_write_c(2, msg);
  lk_write_c(2, "\n");
  lk_trace();
  lk_die(101);
}

static void lk_unreachable(void) __attribute__((noreturn, unused));
static void lk_unreachable(void) { lk_panic_c("内部错误：执行到了不可达代码"); }

static void lk_index_oob(int64_t i, int64_t n) __attribute__((noreturn, unused));
static void lk_index_oob(int64_t i, int64_t n) {
  lk_flush_out();
  lk_errf("panic: 下标越界：%" PRId64 "，长度 %" PRId64 "\n", i, n);
  lk_trace();
  lk_die(101);
}

// 内存分配：运行时和生成的代码都只通过 lk_alloc / lk_realloc / lk_free 申请和释放。默认用 C 的 calloc / realloc / free；
// 没有 C 库的环境（或者要用自己的分配器）在包含这个文件之前定义三个宏（比如编译时 -DLK_MALLOC=my_malloc …）：
//   LK_MALLOC(n)、LK_REALLOC(p, n)、LK_FREE(p)，语义和 malloc / realloc / free 一样（失败时返回 NULL）。
// 只定义一部分时其余的仍用 C 库的。lk_alloc 给出的内存总是清零的（定义了 LK_MALLOC 时由这里 memset）
#ifdef LK_MALLOC
static void* lk_zalloc_(size_t n) {
  void* p = LK_MALLOC(n);
  if (p) memset(p, 0, n);
  return p;
}
#else
#define lk_zalloc_(n) calloc(1, (n))
#endif
#ifndef LK_REALLOC
#define LK_REALLOC(p, n) realloc((p), (n))
#endif
#ifndef LK_FREE
#define LK_FREE(p) free(p)
#endif

static void* lk_alloc(size_t n) {
  void* p = lk_zalloc_(n ? n : 1);
  if (!p) lk_panic_c("内存不足");
  return p;
}

static void* lk_realloc(void* p, size_t n) {
  void* q = LK_REALLOC(p, n ? n : 1);
  if (!q) lk_panic_c("内存不足");
  return q;
}

static inline void lk_free(void* p) { LK_FREE(p); }

// 不 panic 的版本：内存不足时返回 NULL，调用的地方自己报错（子进程那边用）
static void* __attribute__((unused)) lk_try_alloc(size_t n) { return lk_zalloc_(n ? n : 1); }

static void* __attribute__((unused)) lk_try_realloc(void* p, size_t n) { return LK_REALLOC(p, n ? n : 1); }

// ---------- Fn 闭包的环境 ----------
// 堆上的环境以 lk_env 开头：引用计数（见 lk_rc_inc）和释放捕获副本的函数，后面是捕获的值。
typedef struct lk_env {
  int64_t rc;
  void (*drop)(void*);
} lk_env;

// ---------- 字符串 ----------
// 不可变、引用计数（有别的线程时用原子操作，见下面的 lk_rc_inc），可以跨线程共享；rc < 0 表示常驻（字面量），dup / drop 都不影响它。
// 只有 rc == 1 时 lk_str_append 才会原地追加。
typedef struct lk_strobj {
  int64_t rc;
  int64_t len;
  int64_t cap;
  char data[];
} lk_strobj;
typedef lk_strobj* lk_str;

static lk_str lk_str_alloc(int64_t cap) {
  lk_str s = (lk_str)lk_alloc(sizeof(lk_strobj) + (size_t)cap + 1);
  s->rc = 1;
  s->len = 0;
  s->cap = cap;
  return s;
}

static lk_str lk_str_from(const char* p, int64_t n) {
  lk_str s = lk_str_alloc(n);
  memcpy(s->data, p, (size_t)n);
  s->data[n] = 0;
  s->len = n;
  return s;
}

// 第一次用到时创建；多个线程同时第一次用到时只留一个，其余的释放
static lk_str __attribute__((unused)) lk_lit(lk_str* slot, const char* p, int64_t n) {
  lk_str cur = __atomic_load_n(slot, __ATOMIC_ACQUIRE);
  if (cur) return cur;
  lk_str s = lk_str_from(p, n);
  s->rc = -1;
  lk_str expected = NULL;
  if (__atomic_compare_exchange_n(slot, &expected, s, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) return s;
  lk_free(s);
  return expected;
}

static lk_str __attribute__((unused)) lk_str_new(void) { return lk_str_alloc(16); }

// ---------- 引用计数 ----------
// 字符串、Fn 的环境、shared 的计数只在有别的任务活着时才用原子操作。
// lk_nthreads 是 spawn 了、还没结束的任务数：spawn 时（任务能运行之前）加一，任务结束时在调度器的锁里减一。
// 为什么普通加减是安全的：并发是结构化的（scope 块尾等所有任务结束），所以
// - 一个任务只要还活着就被计在里面，它自己读到的总不是 0；spawn 它的任务在它结束之前读到的也不是 0；
// - 计数从 0 变 1 之前的普通加减先于任务开始运行，从 1 变 0 之后的普通加减晚于最后一个任务结束（中间隔着调度器的锁或 runnext 的原子交换），
//   都不会和别的任务同时进行。调度器的工作线程不碰 Lark 的值。
static int64_t lk_nthreads = 0;

#ifdef LK_CORE
// 只带核心时没有任务：引用计数总是普通加减，调用栈总挂在 lk_main_top 上
static inline bool lk_mt(void) { return false; }
#ifndef LK_NOTRACE
static inline lk_frame** lk_slot(void) { return &lk_main_top; }
#endif
#else
static inline bool lk_mt(void) { return __atomic_load_n(&lk_nthreads, __ATOMIC_RELAXED) != 0; }

#ifndef LK_NOTRACE
// 不能内联：任务在等待时可能换到别的系统线程，内联后编译器可能把上一次算出的 __thread 变量地址
// （原来那个线程的）留着再用。每次都调用函数就会重新取当前线程的。
static __attribute__((noinline)) lk_frame** lk_slot_mt(void) {
  lk_frame** s = lk_slot_;
  if (!s) { s = &lk_top_; lk_slot_ = s; }
  return s;
}

static inline lk_frame** lk_slot(void) {
  if (!lk_mt()) return &lk_main_top;
  return lk_slot_mt();
}
#endif
#endif

static inline void lk_rc_inc(int64_t* rc) {
  if (lk_mt()) __atomic_fetch_add(rc, 1, __ATOMIC_RELAXED);
  else ++*rc;
}

// 读计数。有别的任务时，别的线程可能正在原子地加减它，所以也要原子地读，否则在 C 的内存模型里是数据竞争：
// - 只看是不是常驻（rc < 0，建好以后不会变）时用 relaxed，和普通的读一样快；
// - 看是不是只有自己一个持有者（rc == 1，然后就地修改）时用 acquire：和别的线程最后一次 lk_rc_dec 的 release 配对，
//   保证它放手之前对内容的读，都发生在这边改内容之前
static inline int64_t lk_rc_peek(int64_t* rc) {
  return lk_mt() ? __atomic_load_n(rc, __ATOMIC_RELAXED) : *rc;
}

static inline bool lk_rc_unique(int64_t* rc) {
  return (lk_mt() ? __atomic_load_n(rc, __ATOMIC_ACQUIRE) : *rc) == 1;
}

// 减一，返回减后的值
static inline int64_t lk_rc_dec(int64_t* rc) {
  return lk_mt() ? __atomic_sub_fetch(rc, 1, __ATOMIC_ACQ_REL) : --*rc;
}

static lk_str lk_str_dup(lk_str s) {
  if (s && lk_rc_peek(&s->rc) > 0) lk_rc_inc(&s->rc);
  return s;
}

static void __attribute__((unused)) lk_drop_s(lk_str* p) {
  lk_str s = *p;
  *p = NULL;
  if (s && lk_rc_peek(&s->rc) > 0 && lk_rc_dec(&s->rc) == 0) lk_free(s);
}

static lk_str __attribute__((unused)) lk_copy_s(lk_str* p) { return lk_str_dup(*p); }

static int64_t lk_str_len(lk_str s) { return s ? s->len : 0; }
static const char* lk_str_ptr(lk_str s) { return s ? s->data : ""; }

// p 可以指向 *dst 自己（s += s）：换了新的缓冲时，旧的要等复制完再释放
static void lk_str_append_raw(lk_str* dst, const char* p, int64_t n) {
  lk_str d = *dst, old = NULL;
  if (!d || !lk_rc_unique(&d->rc) || d->len + n > d->cap) {
    int64_t len = lk_str_len(d);
    int64_t cap = (len + n) * 2 + 16;
    lk_str nd = lk_str_alloc(cap);
    memcpy(nd->data, lk_str_ptr(d), (size_t)len);
    nd->len = len;
    old = d;
    d = nd;
  }
  memcpy(d->data + d->len, p, (size_t)n);
  d->len += n;
  d->data[d->len] = 0;
  *dst = d;
  if (old) lk_drop_s(&old);
}

static void __attribute__((unused)) lk_str_append(lk_str* dst, lk_str s) {
  lk_str_append_raw(dst, lk_str_ptr(s), lk_str_len(s));
}

static void __attribute__((unused)) lk_str_append_int(lk_str* dst, int64_t v) {
  char buf[32];
  int n = snprintf(buf, sizeof buf, "%" PRId64, v);
  lk_str_append_raw(dst, buf, n);
}

static void __attribute__((unused)) lk_str_append_bool(lk_str* dst, bool b) {
  if (b) lk_str_append_raw(dst, "true", 4);
  else lk_str_append_raw(dst, "false", 5);
}

// 插值里列表、T?、元组的拼接（lk_show_*）用
static void __attribute__((unused)) lk_str_append_c(lk_str* dst, const char* s) {
  lk_str_append_raw(dst, s, (int64_t)strlen(s));
}

static void __attribute__((unused)) lk_str_append_quoted(lk_str* dst, lk_str s) {
  lk_str_append_raw(dst, "\"", 1);
  lk_str_append(dst, s);
  lk_str_append_raw(dst, "\"", 1);
}

static lk_str __attribute__((unused)) lk_str_cat(lk_str a, lk_str b) {
  int64_t na = lk_str_len(a), nb = lk_str_len(b);
  lk_str s = lk_str_alloc(na + nb);
  memcpy(s->data, lk_str_ptr(a), (size_t)na);
  memcpy(s->data + na, lk_str_ptr(b), (size_t)nb);
  s->len = na + nb;
  s->data[s->len] = 0;
  return s;
}

static bool __attribute__((unused)) lk_str_eq(lk_str a, lk_str b) {
  int64_t n = lk_str_len(a);
  return n == lk_str_len(b) && memcmp(lk_str_ptr(a), lk_str_ptr(b), (size_t)n) == 0;
}

static int __attribute__((unused)) lk_str_cmp(lk_str a, lk_str b) {
  int64_t na = lk_str_len(a), nb = lk_str_len(b);
  int c = memcmp(lk_str_ptr(a), lk_str_ptr(b), (size_t)(na < nb ? na : nb));
  if (c != 0) return c;
  return na < nb ? -1 : (na > nb ? 1 : 0);
}

static int64_t __attribute__((unused)) lk_byte_at(lk_str s, int64_t i) {
  if (i < 0 || i >= lk_str_len(s)) lk_index_oob(i, lk_str_len(s));
  return (unsigned char)s->data[i];
}

static lk_str __attribute__((unused)) lk_slice(lk_str s, int64_t a, int64_t b) {
  int64_t n = lk_str_len(s);
  if (a < 0 || b < a || b > n) lk_panic_c("slice：范围无效");
  return lk_str_from(lk_str_ptr(s) + a, b - a);
}

static lk_str __attribute__((unused)) lk_from_byte(int64_t b) {
  char c = (char)b;
  return lk_str_from(&c, 1);
}

static lk_str __attribute__((unused)) lk_int_str(int64_t v) {
  char buf[32];
  int n = snprintf(buf, sizeof buf, "%" PRId64, v);
  return lk_str_from(buf, n);
}

static int64_t __attribute__((unused)) lk_parse_int(lk_str s) {
  const char* p = lk_str_ptr(s);
  char* end;
  long long v = strtoll(p, &end, 10);
  if (lk_str_len(s) == 0 || *end != 0) lk_panic_c("parse_int：不是整数");
  return (int64_t)v;
}

// 先算出总长度，一次分配到位，再逐段复制（不用边拼边扩容）
static lk_str __attribute__((unused)) lk_join_arr(lk_str* xs, int64_t n, lk_str sep) {
  int64_t sl = lk_str_len(sep);
  int64_t total = n > 0 ? sl * (n - 1) : 0;
  for (int64_t i = 0; i < n; i++) total += lk_str_len(xs[i]);
  lk_str r = lk_str_alloc(total);
  char* p = r->data;
  for (int64_t i = 0; i < n; i++) {
    if (i > 0 && sl > 0) { memcpy(p, sep->data, (size_t)sl); p += sl; }
    int64_t k = lk_str_len(xs[i]);
    memcpy(p, lk_str_ptr(xs[i]), (size_t)k);
    p += k;
  }
  r->len = total;
  r->data[total] = 0;
  return r;
}

// ---------- 整数 ----------
// int 是 64 位有符号整数。lark1 生成的 + - * 和一元 - 都经过下面的函数：结果超出范围时 panic，
// 而不是悄悄回绕（C 里有符号溢出是未定义行为）。编译 C 时加 -DLK_UNCHECKED 可以关掉这些检查：
// 这时按 64 位补码回绕（在 uint64_t 上算，C 编译器不能假设不溢出）。
#ifdef LK_UNCHECKED
#define lk_add(a, b) ((int64_t)((uint64_t)(a) + (uint64_t)(b)))
#define lk_sub(a, b) ((int64_t)((uint64_t)(a) - (uint64_t)(b)))
#define lk_mul(a, b) ((int64_t)((uint64_t)(a) * (uint64_t)(b)))
#define lk_neg(a) ((int64_t)(0 - (uint64_t)(a)))
#else
static inline int64_t __attribute__((unused)) lk_add(int64_t a, int64_t b) {
  int64_t r;
  if (__builtin_add_overflow(a, b, &r)) lk_panic_c("整数溢出：加法的结果超出 64 位");
  return r;
}

static inline int64_t __attribute__((unused)) lk_sub(int64_t a, int64_t b) {
  int64_t r;
  if (__builtin_sub_overflow(a, b, &r)) lk_panic_c("整数溢出：减法的结果超出 64 位");
  return r;
}

static inline int64_t __attribute__((unused)) lk_mul(int64_t a, int64_t b) {
  int64_t r;
  if (__builtin_mul_overflow(a, b, &r)) lk_panic_c("整数溢出：乘法的结果超出 64 位");
  return r;
}

static inline int64_t __attribute__((unused)) lk_neg(int64_t a) {
  if (a == INT64_MIN) lk_panic_c("整数溢出：最小的 int 没有相反数");
  return -a;
}
#endif

static int64_t __attribute__((unused)) lk_div(int64_t a, int64_t b) {
  if (b == 0) lk_panic_c("除以零");
  if (a == INT64_MIN && b == -1) lk_panic_c("整数溢出：最小的 int 除以 -1");
  return a / b;
}

static int64_t __attribute__((unused)) lk_mod(int64_t a, int64_t b) {
  if (b == 0) lk_panic_c("除以零");
  if (b == -1) return 0;     // INT64_MIN % -1 在 C 里也会溢出
  return a % b;
}

// 回绕的 +% -% *%：按 64 位补码回绕，不检查溢出（在 uint64_t 上算，避免 C 的未定义行为）
#define lk_wadd(a, b) ((int64_t)((uint64_t)(a) + (uint64_t)(b)))
#define lk_wsub(a, b) ((int64_t)((uint64_t)(a) - (uint64_t)(b)))
#define lk_wmul(a, b) ((int64_t)((uint64_t)(a) * (uint64_t)(b)))

// 移位：<< 移出的位丢掉，>> 左边补符号位，>>> 左边补 0。移位数不在 0..63 时 panic；
// 加了 -DLK_UNCHECKED 时不检查，移位数只取低 6 位（同 x86 和 Java）
#ifdef LK_UNCHECKED
#define lk_shift_n(n) ((n) & 63)
#else
static inline int64_t __attribute__((unused)) lk_shift_n(int64_t n) {
  if (n < 0 || n > 63) lk_panic_c("移位数超出 0..63");
  return n;
}
#endif
#define lk_shl(a, n) ((int64_t)((uint64_t)(a) << lk_shift_n(n)))
#define lk_shr(a, n) ((int64_t)(a) >> lk_shift_n(n))
#define lk_ushr(a, n) ((int64_t)((uint64_t)(a) >> lk_shift_n(n)))

// ---------- 浮点数 ----------
// float 是 C 的 double（IEEE 754）。显示时用能原样读回的最短写法：1.0、0.1、123.456、1e+20、
// inf、-inf、nan；整数值也带 .0，好和 int 区分。指数在 [-5, 17) 之间时不用科学计数法。
static int __attribute__((unused)) lk_fmt_float(char* buf, size_t cap, double v) {
  if (isnan(v)) return snprintf(buf, cap, "nan");
  if (isinf(v)) return snprintf(buf, cap, v < 0 ? "-inf" : "inf");
  if (v == 0) return snprintf(buf, cap, signbit(v) ? "-0.0" : "0.0");
  char e[48];
  int p = 1;
  for (; p < 17; p++) {
    snprintf(e, sizeof e, "%.*e", p - 1, v);
    if (strtod(e, NULL) == v) break;
  }
  snprintf(e, sizeof e, "%.*e", p - 1, v);
  int x = atoi(strchr(e, 'e') + 1);
  if (x < -5 || x >= 17) return snprintf(buf, cap, "%s", e);
  int d = p - 1 - x;
  int n = snprintf(buf, cap, "%.*f", d > 0 ? d : 0, v);
  if (!strchr(buf, '.')) n += snprintf(buf + n, cap - (size_t)n, ".0");
  return n;
}

static void __attribute__((unused)) lk_str_append_float(lk_str* dst, double v) {
  char buf[64];
  int n = lk_fmt_float(buf, sizeof buf, v);
  lk_str_append_raw(dst, buf, n);
}

static lk_str __attribute__((unused)) lk_float_str(double v) {
  char buf[64];
  int n = lk_fmt_float(buf, sizeof buf, v);
  return lk_str_from(buf, n);
}

// 整个字符串都是一个数（strtod 能读的写法：1.5、-2e3、inf、nan……）时为 true
static bool __attribute__((unused)) lk_read_float(lk_str s, double* out) {
  const char* p = lk_str_ptr(s);
  if (lk_str_len(s) == 0 || *p == ' ' || *p == '\t' || *p == '\n') return false;
  char* end;
  *out = strtod(p, &end);
  return *end == 0;
}

static double __attribute__((unused)) lk_parse_float(lk_str s) {
  double v;
  if (!lk_read_float(s, &v)) lk_panic_c("parse_float：不是数");
  return v;
}

static double __attribute__((unused)) lk_try_parse_float(lk_str s, lk_str* err) {
  double v;
  if (!lk_read_float(s, &v)) {
    lk_str e = lk_str_new();
    lk_str_append_raw(&e, "不是数：", (int64_t)strlen("不是数："));
    lk_str_append(&e, s);
    *err = e;
    return 0;
  }
  return v;
}

// 向零取整；nan 和超出 int 范围的值 panic（C 里直接转换是未定义行为）
static int64_t __attribute__((unused)) lk_to_int(double v) {
  if (isnan(v)) lk_panic_c("to_int：nan 不能转成 int");
  if (!(v >= -9223372036854775808.0 && v < 9223372036854775808.0)) lk_panic_c("to_int：超出 int 的范围");
  return (int64_t)v;
}

// u8：to_u8 超出 0..255 时 panic；wrap_u8 只取低 8 位
static uint8_t __attribute__((unused)) lk_to_u8(int64_t v) {
  if (v < 0 || v > 255) {
    char m[80];
    snprintf(m, sizeof m, "to_u8：%" PRId64 " 超出 u8 的范围 0..255", v);
    lk_panic_c(m);
  }
  return (uint8_t)v;
}

static uint8_t __attribute__((unused)) lk_wrap_u8(int64_t v) { return (uint8_t)(v & 0xFF); }

// u16、u32、i32：n.to_u16() 超出范围时 panic，n.wrap_u16() 只取低 16 位（i32 按补码解释低 32 位）
#define LK_FIXED_CONV(N, T, LO, HI, RANGE)                                                   \
  static T __attribute__((unused)) lk_to_##N(int64_t v) {                                  \
    if (v < (LO) || v > (HI)) {                                                             \
      char m[96];                                                                           \
      snprintf(m, sizeof m, "to_" #N "：%" PRId64 " 超出 " #N " 的范围 " RANGE, v);         \
      lk_panic_c(m);                                                                        \
    }                                                                                       \
    return (T)v;                                                                            \
  }
LK_FIXED_CONV(u16, uint16_t, 0, 65535, "0..65535")
LK_FIXED_CONV(u32, uint32_t, 0, INT64_C(4294967295), "0..4294967295")
LK_FIXED_CONV(i32, int32_t, INT64_C(-2147483648), INT64_C(2147483647), "-2147483648..2147483647")

static uint16_t __attribute__((unused)) lk_wrap_u16(int64_t v) { return (uint16_t)(v & 0xFFFF); }
static uint32_t __attribute__((unused)) lk_wrap_u32(int64_t v) { return (uint32_t)(v & 0xFFFFFFFF); }
static int32_t __attribute__((unused)) lk_wrap_i32(int64_t v) {
  uint32_t u = (uint32_t)(v & 0xFFFFFFFF);
  return u > 0x7FFFFFFF ? (int32_t)((int64_t)u - INT64_C(4294967296)) : (int32_t)u;
}

// ---------- extern "c"（调用 C 函数） ----------
// 编译器把 extern "c" { fn name(…) } 声明成 lkc_name，再用汇编标号绑到 C 的符号 name 上：
// 这样不会和系统头文件里的同名声明冲突（参数写法不同也没关系），符号前缀（macOS 是 _）由编译器给出
#define LK_STR2_(x) #x
#define LK_STR_(x) LK_STR2_(x)
#ifdef __USER_LABEL_PREFIX__
#define LK_CSYM(n) __asm__(LK_STR_(__USER_LABEL_PREFIX__) n)
#else
#define LK_CSYM(n) __asm__(n)
#endif

// int 传给 C 的窄整数：超出范围时 panic（不悄悄截断）
static void lk_c_range(const char* fn, const char* ty, int64_t v) __attribute__((noreturn, unused));
static void lk_c_range(const char* fn, const char* ty, int64_t v) {
  char m[160];
  snprintf(m, sizeof m, "%s：参数 %" PRId64 " 超出 %s 的范围", fn, v, ty);
  lk_panic_c(m);
}

static int __attribute__((unused)) lk_c_int(const char* fn, int64_t v) {
  if (v < INT32_MIN || v > INT32_MAX) lk_c_range(fn, "c_int", v);
  return (int)v;
}

static unsigned int __attribute__((unused)) lk_c_uint(const char* fn, int64_t v) {
  if (v < 0 || v > (int64_t)UINT32_MAX) lk_c_range(fn, "c_uint", v);
  return (unsigned int)v;
}

static size_t __attribute__((unused)) lk_c_usize(const char* fn, int64_t v) {
  if (v < 0) lk_c_range(fn, "usize", v);
  return (size_t)v;
}

static unsigned long __attribute__((unused)) lk_c_ulong(const char* fn, int64_t v) {
  if (v < 0) lk_c_range(fn, "c_ulong", v);
  return (unsigned long)v;
}

// C 返回的无符号数放不进 int 时 panic
static int64_t __attribute__((unused)) lk_c_unsigned_ret(const char* fn, unsigned long long v) {
  if (v > (unsigned long long)INT64_MAX) {
    char m[160];
    snprintf(m, sizeof m, "%s：返回值 %llu 超出 int 的范围", fn, v);
    lk_panic_c(m);
  }
  return (int64_t)v;
}

// C 返回的字符串（以 0 结尾）复制一份；NULL 当作空串。C 那边的内存不归 Lark 管
static lk_str __attribute__((unused)) lk_c_str(const char* p) { return p ? lk_str_from(p, (int64_t)strlen(p)) : lk_str_from("", 0); }

// ---------- I/O 与进程 ----------
// 整行一起输出，多个线程同时 print 时不会交错
// （只带核心时没有别的线程，不用加锁）
#ifdef LK_CORE
#define lk_flock(f) ((void)0)
#define lk_funlock(f) ((void)0)
#else
#define lk_flock(f) flockfile(f)
#define lk_funlock(f) funlockfile(f)
#endif
static void __attribute__((unused)) lk_print(lk_str s) {
  lk_flock(stdout);
  lark_plat_write(1, lk_str_ptr(s), (size_t)lk_str_len(s));
  lark_plat_write(1, "\n", 1);
  lk_funlock(stdout);
}

static void __attribute__((unused)) lk_eprint(lk_str s) {
  lk_flock(stderr);
  lark_plat_write(2, lk_str_ptr(s), (size_t)lk_str_len(s));
  lark_plat_write(2, "\n", 1);
  lk_funlock(stderr);
}

static void __attribute__((unused, noreturn)) lk_panic(lk_str s) {
  lk_flush_out();
  lk_write_c(2, "panic: ");
  lark_plat_write(2, lk_str_ptr(s), (size_t)lk_str_len(s));
  lk_write_c(2, "\n");
  lk_trace();
  lk_die(101);
}

// ---------- 哈希：std/map 用 ----------
// 字符串的哈希是 SipHash-1-3（Rust 的 HashMap 默认也是它），密钥在进程启动后第一次用到时从系统随机数取：
// 别人看不到密钥，就没法专门造一批哈希相同的键，把哈希表拖慢成线性查找（哈希洪水攻击）。
// 每次运行的哈希值不一样；Map 按插入顺序遍历，所以程序的输出不受影响。
// 按本机字节序一次读 8 个字节：只在同一个进程里比较，不用跨机器一致
int64_t lark_siphash(const char* p, int64_t n);
int64_t lark_hash_seed(void);

static uint64_t lk_hash_k0, lk_hash_k1;
static void lk_hash_init(void);
#ifdef LK_CORE
static bool lk_hash_ready;
#define LK_HASH_ONCE() do { if (!lk_hash_ready) { lk_hash_ready = true; lk_hash_init(); } } while (0)
#else
static pthread_once_t lk_hash_once = PTHREAD_ONCE_INIT;
#define LK_HASH_ONCE() pthread_once(&lk_hash_once, lk_hash_init)
#endif

static void lk_hash_init(void) {
  uint64_t k[2] = {0, 0};
  lark_plat_random(k, sizeof k);
  lk_hash_k0 = k[0];
  lk_hash_k1 = k[1];
}

#define LK_ROTL(x, b) (uint64_t)(((x) << (b)) | ((x) >> (64 - (b))))
#define LK_SIPROUND do { \
    v0 += v1; v1 = LK_ROTL(v1, 13); v1 ^= v0; v0 = LK_ROTL(v0, 32); \
    v2 += v3; v3 = LK_ROTL(v3, 16); v3 ^= v2; \
    v0 += v3; v3 = LK_ROTL(v3, 21); v3 ^= v0; \
    v2 += v1; v1 = LK_ROTL(v1, 17); v1 ^= v2; v2 = LK_ROTL(v2, 32); \
  } while (0)

__attribute__((used)) int64_t lark_siphash(const char* p, int64_t n) {
  LK_HASH_ONCE();
  uint64_t v0 = 0x736f6d6570736575ULL ^ lk_hash_k0, v1 = 0x646f72616e646f6dULL ^ lk_hash_k1;
  uint64_t v2 = 0x6c7967656e657261ULL ^ lk_hash_k0, v3 = 0x7465646279746573ULL ^ lk_hash_k1;
  const uint8_t* s = (const uint8_t*)p;
  int64_t end = n - n % 8;
  for (int64_t i = 0; i < end; i += 8) {
    uint64_t m;
    memcpy(&m, s + i, 8);
    v3 ^= m;
    LK_SIPROUND;
    v0 ^= m;
  }
  uint64_t b = (uint64_t)n << 56;
  for (int64_t i = end; i < n; i++) b |= (uint64_t)s[i] << (8 * (i - end));
  v3 ^= b;
  LK_SIPROUND;
  v0 ^= b;
  v2 ^= 0xff;
  LK_SIPROUND;
  LK_SIPROUND;
  LK_SIPROUND;
  return (int64_t)(v0 ^ v1 ^ v2 ^ v3);
}

// 每个 Map 一个种子（密钥加上一个计数，再用 splitmix64 打散）：槽位由种子和键的哈希一起决定，
// 自己写的、没有密钥的 hash 也就猜不出会落在哪个槽；两个 Map 的槽位顺序也不同，
// 把一个大 Map 的键按顺序插进另一个时，线性探测不会越挤越长
__attribute__((used)) int64_t lark_hash_seed(void) {
  static int64_t ctr;
  LK_HASH_ONCE();
#ifdef LK_CORE
  uint64_t x = lk_hash_k0 + (uint64_t)(++ctr) * 0x9E3779B97F4A7C15ULL;
#else
  uint64_t x = lk_hash_k0 + (uint64_t)__atomic_add_fetch(&ctr, 1, __ATOMIC_RELAXED) * 0x9E3779B97F4A7C15ULL;
#endif
  x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
  x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
  return (int64_t)(x ^ (x >> 31));
}

// ---------- 退出钩子：os.at_exit ----------
// 登记的 Fn() -> () 在进程退出时按登记的逆序各跑一次：main 正常结束、exit、panic 都算（底下是 C 的 atexit）。
// 闭包的环境计数加一留在这里，到进程结束都不释放
typedef struct { void (*f)(void*); void* env; } lk_hook;
#ifndef LK_CORE
void lark_at_exit(lk_hook h);
#endif

// 登记钩子的是 std/os（系统层），只带核心时用不到
#ifndef LK_CORE
static pthread_mutex_t lk_hook_mu = PTHREAD_MUTEX_INITIALIZER;
static lk_hook* lk_hooks;
static int64_t lk_nhooks, lk_hooks_cap;

static void lk_run_hooks(void) {
  lk_exiting = 1;
  fflush(stdout);
  for (;;) {
    pthread_mutex_lock(&lk_hook_mu);
    if (lk_nhooks == 0) {
      pthread_mutex_unlock(&lk_hook_mu);
      break;
    }
    lk_hook h = lk_hooks[--lk_nhooks];
    pthread_mutex_unlock(&lk_hook_mu);
    h.f(h.env);
    fflush(stdout);
  }
}

__attribute__((used)) void lark_at_exit(lk_hook h) {
  pthread_mutex_lock(&lk_hook_mu);
  if (lk_hooks_cap == 0) atexit(lk_run_hooks);
  if (lk_nhooks == lk_hooks_cap) {
    lk_hooks_cap = lk_hooks_cap ? lk_hooks_cap * 2 : 4;
    lk_hooks = (lk_hook*)lk_realloc(lk_hooks, (size_t)lk_hooks_cap * sizeof(lk_hook));
  }
  if (h.env) lk_rc_inc(&((lk_env*)h.env)->rc);
  lk_hooks[lk_nhooks++] = h;
  pthread_mutex_unlock(&lk_hook_mu);
}
#endif

static void __attribute__((unused, noreturn)) lk_exit(int64_t code) {
  lk_flush_out();
  lk_die((int)code);
}

#ifdef LK_BARE
// 没有文件系统和子进程：调用到了就 panic（try_read_file 返回错误）
static lk_str __attribute__((unused)) lk_read_file(lk_str path) {
  (void)path;
  lk_panic_c("read_file：没有文件系统（LK_BARE）");
}

static void __attribute__((unused)) lk_write_file(lk_str path, lk_str data) {
  (void)path;
  (void)data;
  lk_panic_c("write_file：没有文件系统（LK_BARE）");
}

static int64_t __attribute__((unused)) lk_system(lk_str cmd) {
  (void)cmd;
  lk_panic_c("system：没有子进程（LK_BARE）");
}

static lk_str __attribute__((unused)) lk_try_read_file(lk_str path, lk_str* err) {
  (void)path;
  *err = lk_str_from("没有文件系统（LK_BARE）", (int64_t)strlen("没有文件系统（LK_BARE）"));
  return NULL;
}
#else
static lk_str __attribute__((unused)) lk_read_file(lk_str path) {
  FILE* f = fopen(lk_str_ptr(path), "rb");
  if (!f) {
    fprintf(stderr, "无法读取文件 %s\n", lk_str_ptr(path));
    lk_die(1);
  }
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  fseek(f, 0, SEEK_SET);
  lk_str s = lk_str_alloc(n);
  if (n > 0 && fread(s->data, 1, (size_t)n, f) != (size_t)n) lk_panic_c("读取文件失败");
  s->len = n;
  s->data[n] = 0;
  fclose(f);
  return s;
}

static void __attribute__((unused)) lk_write_file(lk_str path, lk_str data) {
  FILE* f = fopen(lk_str_ptr(path), "wb");
  if (!f) {
    fprintf(stderr, "无法写入文件 %s\n", lk_str_ptr(path));
    lk_die(1);
  }
  fwrite(lk_str_ptr(data), 1, (size_t)lk_str_len(data), f);
  fclose(f);
}

static int64_t __attribute__((unused)) lk_system(lk_str cmd) {
  fflush(stdout);
  return (int64_t)system(lk_str_ptr(cmd));
}

// ---------- 可能失败的 I/O：失败时把错误信息写进 *err，成功时 *err 保持 NULL ----------
static lk_str __attribute__((unused)) lk_try_read_file(lk_str path, lk_str* err) {
  FILE* f = fopen(lk_str_ptr(path), "rb");
  if (!f) {
    lk_str e = lk_str_new();
    lk_str_append_raw(&e, "无法读取文件 ", (int64_t)strlen("无法读取文件 "));
    lk_str_append(&e, path);
    *err = e;
    return NULL;
  }
  fseek(f, 0, SEEK_END);
  long n = ftell(f);
  fseek(f, 0, SEEK_SET);
  lk_str s = lk_str_alloc(n);
  if (n > 0 && fread(s->data, 1, (size_t)n, f) != (size_t)n) {
    fclose(f);
    lk_drop_s(&s);
    *err = lk_str_from("读取文件失败", (int64_t)strlen("读取文件失败"));
    return NULL;
  }
  s->len = n;
  s->data[n] = 0;
  fclose(f);
  return s;
}
#endif

static int64_t __attribute__((unused)) lk_try_parse_int(lk_str s, lk_str* err) {
  const char* p = lk_str_ptr(s);
  char* end;
  errno = 0;
  long long v = strtoll(p, &end, 10);
  if (lk_str_len(s) == 0 || *end != 0) {
    lk_str e = lk_str_new();
    lk_str_append_raw(&e, "不是整数：", (int64_t)strlen("不是整数："));
    lk_str_append(&e, s);
    *err = e;
    return 0;
  }
  // 超出 int 的范围时 strtoll 不报错，只把结果卡在最大或最小值上、设置 errno：要自己检查
  if (errno == ERANGE) {
    lk_str e = lk_str_new();
    lk_str_append_raw(&e, "超出 int 的范围：", (int64_t)strlen("超出 int 的范围："));
    lk_str_append(&e, s);
    *err = e;
    return 0;
  }
  return (int64_t)v;
}

#ifndef LK_CORE  // 可选部分（一）：std/os、io、term、proc、time 的时区、signal、net 的底层

// ---------- 文件系统、环境变量、子进程（std/os 用）----------
// 失败时 *err 是 “动作 路径：系统给的原因”，成功时 *err 保持 NULL；没有有用返回值的返回 0。
static lk_str __attribute__((unused)) lk_os_err(const char* what, lk_str path) {
  const char* why = strerror(errno);
  lk_str e = lk_str_new();
  lk_str_append_raw(&e, what, (int64_t)strlen(what));
  lk_str_append(&e, path);
  lk_str_append_raw(&e, "：", (int64_t)strlen("："));
  lk_str_append_raw(&e, why, (int64_t)strlen(why));
  return e;
}

static int64_t __attribute__((unused)) lk_put_file(lk_str path, lk_str data, const char* mode, lk_str* err) {
  FILE* f = fopen(lk_str_ptr(path), mode);
  if (!f) { *err = lk_os_err("无法写入文件 ", path); return 0; }
  size_t n = (size_t)lk_str_len(data);
  bool ok = fwrite(lk_str_ptr(data), 1, n, f) == n;
  if (fclose(f) != 0) ok = false;
  if (!ok) *err = lk_os_err("写入文件失败 ", path);
  return 0;
}

static int64_t __attribute__((unused)) lk_try_write_file(lk_str path, lk_str data, lk_str* err) {
  return lk_put_file(path, data, "wb", err);
}

static int64_t __attribute__((unused)) lk_try_append_file(lk_str path, lk_str data, lk_str* err) {
  return lk_put_file(path, data, "ab", err);
}

// 0 不存在，1 普通文件，2 目录，3 其它（设备、管道等）；符号链接按它指向的东西算
static int64_t __attribute__((unused)) lk_file_kind(lk_str path) {
  struct stat sb;
  if (stat(lk_str_ptr(path), &sb) != 0) return 0;
  if (S_ISREG(sb.st_mode)) return 1;
  if (S_ISDIR(sb.st_mode)) return 2;
  return 3;
}

// 目录里的名字（不含 . 和 ..），每个后面跟一个 \n；顺序由系统决定，std/os 会排序
static lk_str __attribute__((unused)) lk_try_list_dir(lk_str path, lk_str* err) {
  DIR* d = opendir(lk_str_ptr(path));
  if (!d) { *err = lk_os_err("无法读取目录 ", path); return NULL; }
  lk_str out = lk_str_new();
  struct dirent* ent;
  while ((ent = readdir(d)) != NULL) {
    const char* n = ent->d_name;
    if (strcmp(n, ".") == 0 || strcmp(n, "..") == 0) continue;
    lk_str_append_raw(&out, n, (int64_t)strlen(n));
    lk_str_append_raw(&out, "\n", 1);
  }
  closedir(d);
  return out;
}

// ---------- 文件描述符（std/io 的底层） ----------
// mode："r" 读，"w" 写（清空或新建），"a" 追加（不存在时新建）；得到文件描述符
static int64_t __attribute__((unused)) lk_try_open(lk_str path, lk_str mode, lk_str* err) {
  const char* m = lk_str_ptr(mode);
  int flags;
  if (strcmp(m, "r") == 0) flags = O_RDONLY;
  else if (strcmp(m, "w") == 0) flags = O_WRONLY | O_CREAT | O_TRUNC;
  else if (strcmp(m, "a") == 0) flags = O_WRONLY | O_CREAT | O_APPEND;
  else { *err = lk_str_from("打开方式只能是 r、w、a", (int64_t)strlen("打开方式只能是 r、w、a")); return -1; }
  int fd;
  do { fd = open(lk_str_ptr(path), flags | O_CLOEXEC, 0666); } while (fd < 0 && errno == EINTR);
  if (fd < 0) { *err = lk_os_err("无法打开 ", path); return -1; }
  return fd;
}

// 调度器启动以后，socket 的读写、accept 不再阻塞工作线程：得到 EAGAIN 时让任务挂起，等事件循环叫醒（见“事件循环”）。
// 调度器没有启动时（程序没有用并发）照旧直接阻塞。超时：没启动时靠 SO_RCVTIMEO / SO_SNDTIMEO，启动以后靠 lk_fd_deadline
static bool lk_started;
static bool lk_fd_wait(int fd, bool wr, int64_t deadline);
static int64_t lk_fd_deadline(int fd);
static void lk_fd_set_timeout(int fd, int64_t ms);
static void lk_fd_forget(int fd);
static void lk_fd_nonblock(int fd);

// fd 现在读不会等：有数据、到了结尾、出错（这几种 read 都马上返回）
static bool lk_fd_ready_in(int fd) {
  struct pollfd p = { fd, POLLIN, 0 };
  int r;
  do { r = poll(&p, 1, 0); } while (r < 0 && errno == EINTR);
  return r != 0;
}

static lk_str lk_fd_err(const char* what, int64_t fd) {
  int saved = errno;
  char b[48];
  snprintf(b, sizeof b, "%" PRId64, fd);
  lk_str n = lk_str_from(b, (int64_t)strlen(b));
  errno = saved;
  lk_str e = lk_os_err(what, n);
  lk_drop_s(&n);
  return e;
}

// 超时（EAGAIN）时是 "动作，文件描述符 N：超时"，别的错误照 lk_fd_err。std/net 的 is_timeout 认的就是结尾的“：超时”
static lk_str lk_fd_err_t(const char* what, int64_t fd) {
  if (errno != EAGAIN && errno != EWOULDBLOCK) return lk_fd_err(what, fd);
  char b[160];
  snprintf(b, sizeof b, "%s%" PRId64 "：超时", what, fd);
  return lk_str_from(b, (int64_t)strlen(b));
}

// 最多读 max 个字节；读到结尾时得到空串
static lk_str __attribute__((unused)) lk_try_fd_read(int64_t fd, int64_t max, lk_str* err) {
  if (max <= 0) max = 65536;
  lk_str s = lk_str_alloc(max);
  ssize_t n = -1;
  if (lk_started) {
    // socket 用不等待的 recv，没有数据就挂起任务。
    // 不是 socket（管道、终端、文件）时不能设 O_NONBLOCK：标准输入和父进程（shell）共用同一个打开的文件，改了会影响它们。
    // 所以先用 poll 看有没有数据，没有就同样挂起任务、等事件循环叫醒，醒来再看；普通文件 poll 总是说可读
    int64_t dl = -2;
    bool sock = true;
    for (;;) {
      if (sock) {
        n = recv((int)fd, s->data, (size_t)max, MSG_DONTWAIT);
        if (n >= 0) break;
        if (errno == EINTR) continue;
        if (errno == ENOTSOCK) {
          sock = false;
          continue;
        }
        if (errno != EAGAIN && errno != EWOULDBLOCK) break;
      } else if (lk_fd_ready_in((int)fd)) {
        do { n = read((int)fd, s->data, (size_t)max); } while (n < 0 && errno == EINTR);
        break;
      }
      if (dl == -2) dl = lk_fd_deadline((int)fd);
      if (!lk_fd_wait((int)fd, false, dl)) { errno = EAGAIN; n = -1; break; }
    }
  } else {
    do { n = read((int)fd, s->data, (size_t)max); } while (n < 0 && errno == EINTR);
  }
  if (n < 0) { lk_free(s); *err = lk_fd_err_t("读取失败，文件描述符 ", fd); return NULL; }
  // 读到的比缓冲区小很多时（比如终端一行一行地输入）复制成刚好的大小，不占着整块缓冲区
  if (n < max / 4) {
    lk_str r = lk_str_from(s->data, (int64_t)n);
    lk_free(s);
    return r;
  }
  s->data[n] = 0;
  s->len = n;
  return s;
}

// 把 s 全部写进去（write 可能只写一部分，循环写完）
static int64_t __attribute__((unused)) lk_try_fd_write(int64_t fd, lk_str s, lk_str* err) {
  // print 走的是 stdio 的缓冲区：先把它写出去，顺序才对
  if (fd == 1) fflush(stdout);
  if (fd == 2) fflush(stderr);
  const char* p = lk_str_ptr(s);
  int64_t left = lk_str_len(s);
  while (left > 0) {
    ssize_t n = write((int)fd, p, (size_t)left);
    if (n < 0 && errno == EINTR) continue;
    if (n < 0) { *err = lk_fd_err("写入失败，文件描述符 ", fd); return 0; }
    p += n;
    left -= n;
  }
  return 0;
}

static int64_t __attribute__((unused)) lk_try_fd_close(int64_t fd, lk_str* err) {
  lk_fd_forget((int)fd);
  if (close((int)fd) != 0) *err = lk_fd_err("关闭失败，文件描述符 ", fd);
  return 0;
}

// ---------- 终端（std/term 用 extern "c" 调用，所以不是 static） ----------
// 原始模式改的是标准输入的 termios；进入时登记 atexit，正常退出、exit 和 panic（exit(101)）时都会恢复终端。
// 窗口大小变化（SIGWINCH）只记个数，由程序自己来取。
#include <termios.h>
#include <sys/ioctl.h>
#include <signal.h>

int lark_term_raw(int tenths);
int lark_term_restore(void);
int64_t lark_term_size(int fd);
int64_t lark_term_resizes(void);
void lark_term_alt(int on);

static struct termios lk_term_saved;
static int lk_term_is_raw;
static int lk_term_alt_on;
static int lk_term_hooked;
static volatile sig_atomic_t lk_term_winch;

static void lk_term_on_winch(int sig) { (void)sig; lk_term_winch = lk_term_winch + 1; }

static void lk_term_at_exit(void) { (void)lark_term_restore(); }

// 进入原始模式：不回显、不按行缓冲、不处理 Ctrl-C 等信号键、输出不把 \n 换成 \r\n。
// tenths > 0 时没有输入的 read 最多等 tenths × 0.1 秒就返回空；0 时一直等到有一个字节。成功是 0，失败是 errno
__attribute__((used)) int lark_term_raw(int tenths) {
  if (!isatty(0)) return ENOTTY;
  if (!lk_term_is_raw && tcgetattr(0, &lk_term_saved) != 0) return errno;
  if (!lk_term_hooked) {
    lk_term_hooked = 1;
    atexit(lk_term_at_exit);
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = lk_term_on_winch;
    sa.sa_flags = SA_RESTART;
    sigemptyset(&sa.sa_mask);
    sigaction(SIGWINCH, &sa, NULL);
  }
  struct termios t = lk_term_saved;
  t.c_iflag &= ~(tcflag_t)(BRKINT | ICRNL | INPCK | ISTRIP | IXON);
  t.c_oflag &= ~(tcflag_t)OPOST;
  t.c_cflag |= CS8;
  t.c_lflag &= ~(tcflag_t)(ECHO | ICANON | IEXTEN | ISIG);
  t.c_cc[VMIN] = tenths > 0 ? 0 : 1;
  t.c_cc[VTIME] = (cc_t)(tenths > 255 ? 255 : (tenths < 0 ? 0 : tenths));
  if (tcsetattr(0, TCSAFLUSH, &t) != 0) return errno;
  lk_term_is_raw = 1;
  return 0;
}

// 离开备用屏幕（并显示光标），恢复进入原始模式前的设置；没进入过时什么都不做。成功是 0，失败是 errno
__attribute__((used)) int lark_term_restore(void) {
  fflush(stdout);
  if (lk_term_alt_on) lark_term_alt(0);
  if (!lk_term_is_raw) return 0;
  lk_term_is_raw = 0;
  return tcsetattr(0, TCSAFLUSH, &lk_term_saved) != 0 ? errno : 0;
}

// 行数 << 16 | 列数；不是终端或查不到时 -1
__attribute__((used)) int64_t lark_term_size(int fd) {
  struct winsize w;
  if (ioctl(fd, TIOCGWINSZ, &w) != 0 || w.ws_row == 0 || w.ws_col == 0) return -1;
  return ((int64_t)w.ws_row << 16) | (int64_t)w.ws_col;
}

// 上次调用以来收到几次 SIGWINCH（只在进入过原始模式之后才数）
__attribute__((used)) int64_t lark_term_resizes(void) {
  int64_t n = (int64_t)lk_term_winch;
  lk_term_winch = 0;
  return n;
}

// 换到备用屏幕（退出时原来的内容回来）或者换回来；直接写到文件描述符 1，先把 print 的缓冲写出去
__attribute__((used)) void lark_term_alt(int on) {
  fflush(stdout);
  const char* s = on ? "\033[?1049h" : "\033[?25h\033[?1049l";
  size_t left = strlen(s);
  while (left > 0) {
    ssize_t n = write(1, s, left);
    if (n < 0 && errno == EINTR) continue;
    if (n <= 0) break;
    s += n;
    left -= (size_t)n;
  }
  lk_term_alt_on = on;
}

// ---------- 子进程（std/proc 用 extern "c" 调用） ----------
// posix_spawnp 直接传参数列表，不经过 sh。抓输出时三个管道一起用 poll 读写，子进程写满了一个管道也不会互相等死。
// 结果放在 malloc 的 lk_proc_res 里，句柄就是它的地址；std/proc 取完长度和内容后释放。
// 有超时的时候子进程放进自己的进程组，到时间连它启动的进程一起用 SIGKILL 结束（只在抓输出时用：不和终端打交道）
#include <spawn.h>
#include <poll.h>
extern char** environ;

typedef struct {
  int64_t code;
  int timed_out;
  char* buf[2];
  size_t len[2], cap[2];
} lk_proc_res;

int64_t lark_proc_run(const char* packed, int argc, const uint8_t* in, int64_t in_len, const char* dir, int capture,
                      const char* env, int envc, int64_t timeout_ms);
int64_t lark_proc_code(int64_t h);
int lark_proc_timed_out(int64_t h);
int64_t lark_proc_len(int64_t h, int k);
void lark_proc_copy(int64_t h, int k, uint8_t* dst);
void lark_proc_free(int64_t h);

static int64_t lk_proc_now_ms(void) {
  struct timespec ts;
  clock_gettime(CLOCK_MONOTONIC, &ts);
  return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

// 环境变量的名字：= 前面的部分（没有 = 时是整个）
static size_t lk_env_key(const char* s) {
  const char* e = strchr(s, '=');
  return e ? (size_t)(e - s) : strlen(s);
}

static int lk_env_same(const char* a, const char* b) {
  size_t n = lk_env_key(a);
  return n == lk_env_key(b) && strncmp(a, b, n) == 0;
}

// env 是 envc 个以 0 结尾的 "名字=值"（设置或覆盖）或 "名字"（去掉），在当前环境上改；同一个名字写了几次时最后一次算。
// 返回的数组里的字符串借用 environ 和 env，只释放数组本身
static char** lk_proc_env(const char* env, int envc) {
  size_t n = 0;
  while (environ[n]) n++;
  char** out = lk_try_alloc((n + (size_t)envc + 1) * sizeof *out);
  const char** ch = lk_try_alloc(((size_t)envc + 1) * sizeof *ch);
  if (!out || !ch) { lk_free(out); lk_free(ch); return NULL; }
  const char* p = env;
  for (int i = 0; i < envc; i++) {
    ch[i] = p;
    p += strlen(p) + 1;
  }
  size_t m = 0;
  for (size_t i = 0; i < n; i++) {
    int hit = 0;
    for (int j = 0; j < envc && !hit; j++) hit = lk_env_same(ch[j], environ[i]);
    if (!hit) out[m++] = environ[i];
  }
  for (int j = 0; j < envc; j++) {
    if (!strchr(ch[j], '=')) continue;
    int later = 0;
    for (int k = j + 1; k < envc && !later; k++) later = lk_env_same(ch[j], ch[k]);
    if (!later) out[m++] = (char*)ch[j];
  }
  lk_free(ch);
  return out;
}
static void lk_proc_add(lk_proc_res* r, int k, const char* p, size_t n) {
  if (r->len[k] + n > r->cap[k]) {
    size_t c = r->cap[k] ? r->cap[k] * 2 : 4096;
    while (c < r->len[k] + n) c *= 2;
    char* b = lk_try_realloc(r->buf[k], c);
    if (!b) { fprintf(stderr, "内存不足\n"); exit(101); }
    r->buf[k] = b;
    r->cap[k] = c;
  }
  memcpy(r->buf[k] + r->len[k], p, n);
  r->len[k] += n;
}

// 把 in 写给子进程（win），同时读它的标准输出（rd[0]）和标准错误（rd[1]），直到都关掉；
// deadline 不是 -1 时到点就结束进程组 pid、不再等（它启动的进程可能还拿着管道）
static void lk_proc_pump(lk_proc_res* r, int win, int rout, int rerr, const uint8_t* in, int64_t in_len, pid_t pid, int64_t deadline) {
  // 子进程不读输入就退出时，写管道会收到 SIGPIPE：macOS 可以对这个描述符关掉，别的系统在这个线程里先挡住
#ifdef F_SETNOSIGPIPE
  if (win >= 0) fcntl(win, F_SETNOSIGPIPE, 1);
#else
  sigset_t pipe_set, old_set;
  sigemptyset(&pipe_set);
  sigaddset(&pipe_set, SIGPIPE);
  pthread_sigmask(SIG_BLOCK, &pipe_set, &old_set);
#endif
  if (win >= 0) fcntl(win, F_SETFL, fcntl(win, F_GETFL) | O_NONBLOCK);
  int64_t off = 0;
  int rd[2] = {rout, rerr};
  char buf[16384];
  while (win >= 0 || rd[0] >= 0 || rd[1] >= 0) {
    struct pollfd ps[3];
    int who[3];
    nfds_t n = 0;
    if (win >= 0) { ps[n].fd = win; ps[n].events = POLLOUT; ps[n].revents = 0; who[n++] = 2; }
    for (int k = 0; k < 2; k++) {
      if (rd[k] >= 0) { ps[n].fd = rd[k]; ps[n].events = POLLIN; ps[n].revents = 0; who[n++] = k; }
    }
    int wait_ms = -1;
    if (deadline >= 0) {
      int64_t left = deadline - lk_proc_now_ms();
      if (left <= 0) {
        kill(-pid, SIGKILL);
        r->timed_out = 1;
        break;
      }
      wait_ms = left > 1000000 ? 1000000 : (int)left;
    }
    int got = poll(ps, n, wait_ms);
    if (got == 0) continue;
    if (got < 0) {
      if (errno == EINTR) continue;
      break;
    }
    for (nfds_t i = 0; i < n; i++) {
      if (!ps[i].revents) continue;
      if (who[i] == 2) {
        ssize_t w = write(win, in + off, (size_t)(in_len - off));
        if (w > 0) off += w;
        if ((w < 0 && errno != EAGAIN && errno != EINTR) || off >= in_len) { close(win); win = -1; }
      } else {
        int k = who[i];
        ssize_t m = read(rd[k], buf, sizeof buf);
        if (m > 0) lk_proc_add(r, k, buf, (size_t)m);
        else if (m == 0 || (errno != EINTR && errno != EAGAIN)) { close(rd[k]); rd[k] = -1; }
      }
    }
  }
  if (win >= 0) close(win);
  for (int k = 0; k < 2; k++) {
    if (rd[k] >= 0) close(rd[k]);
  }
#ifndef F_SETNOSIGPIPE
  sigset_t pend;
  sigpending(&pend);
  if (sigismember(&pend, SIGPIPE)) { int sig; sigwait(&pipe_set, &sig); }
  pthread_sigmask(SIG_SETMASK, &old_set, NULL);
#endif
}

// 等子进程结束。deadline 不是 -1 时到点就结束整个进程组，再等它真的退出
static int lk_proc_wait(pid_t pid, int64_t deadline, int* timed_out) {
  int st = 0;
  for (;;) {
    int poll_only = deadline >= 0 && !*timed_out;
    pid_t w = waitpid(pid, &st, poll_only ? WNOHANG : 0);
    if (w == pid) return st;
    if (w < 0) {
      if (errno == EINTR) continue;
      return 0;
    }
    if (lk_proc_now_ms() >= deadline) {
      kill(-pid, SIGKILL);
      *timed_out = 1;
    } else {
      struct timespec ts = {0, 5000000};
      nanosleep(&ts, NULL);
    }
  }
}

// packed 是 argc 个以 0 结尾的参数连在一起；dir 为空时在当前目录运行。
// capture 为 1 时标准输入是 in（in_len 为 0 时是 /dev/null），标准输出和标准错误都抓下来；为 0 时三个都和父进程共用。
// 成功时返回句柄（子进程已经结束），启动不了时返回 -errno
__attribute__((used)) int64_t lark_proc_run(const char* packed, int argc, const uint8_t* in, int64_t in_len, const char* dir, int capture,
                                            const char* env, int envc, int64_t timeout_ms) {
  char** argv = lk_try_alloc(((size_t)argc + 1) * sizeof *argv);
  lk_proc_res* r = lk_try_alloc(sizeof *r);
  char** envp = envc > 0 ? lk_proc_env(env, envc) : environ;
  if (!argv || !r || !envp) {
    lk_free(argv);
    lk_free(r);
    if (envp && envp != environ) lk_free(envp);
    return -ENOMEM;
  }
  const char* p = packed;
  for (int i = 0; i < argc; i++) {
    argv[i] = (char*)p;
    p += strlen(p) + 1;
  }
  int fds[3][2] = {{-1, -1}, {-1, -1}, {-1, -1}};
  int devnull = -1, err = 0;
  posix_spawn_file_actions_t fa;
  posix_spawn_file_actions_init(&fa);
  if (capture) {
    for (int k = 0; k < 3 && !err; k++) {
      if (k == 0 && in_len == 0) continue;
      if (pipe(fds[k]) != 0) { err = errno; break; }
      fcntl(fds[k][0], F_SETFD, FD_CLOEXEC);
      fcntl(fds[k][1], F_SETFD, FD_CLOEXEC);
    }
    if (!err && in_len == 0) {
      devnull = open("/dev/null", O_RDONLY | O_CLOEXEC);
      if (devnull < 0) err = errno;
    }
    if (!err) {
      posix_spawn_file_actions_adddup2(&fa, in_len > 0 ? fds[0][0] : devnull, 0);
      posix_spawn_file_actions_adddup2(&fa, fds[1][1], 1);
      posix_spawn_file_actions_adddup2(&fa, fds[2][1], 2);
    }
  }
  if (!err && dir[0]) {
#if defined(__APPLE__) || (defined(__GLIBC__) && (__GLIBC__ > 2 || (__GLIBC__ == 2 && __GLIBC_MINOR__ >= 29)))
    // macOS 26 起把 _np 版本标成弃用（新名字 posix_spawn_file_actions_addchdir 在旧系统上没有），两边都能用的只有它
#pragma GCC diagnostic push
#pragma GCC diagnostic ignored "-Wdeprecated-declarations"
    err = posix_spawn_file_actions_addchdir_np(&fa, dir);
#pragma GCC diagnostic pop
#else
    err = ENOSYS;
#endif
  }
  pid_t pid = -1;
  if (!err) {
    fflush(stdout);
    fflush(stderr);
    posix_spawnattr_t at;
    posix_spawnattr_init(&at);
    if (timeout_ms > 0) {
      posix_spawnattr_setflags(&at, POSIX_SPAWN_SETPGROUP);
      posix_spawnattr_setpgroup(&at, 0);
    }
    err = posix_spawnp(&pid, argv[0], &fa, &at, argv, envp);
    posix_spawnattr_destroy(&at);
  }
  posix_spawn_file_actions_destroy(&fa);
  lk_free(argv);
  if (envp != environ) lk_free(envp);
  // 子进程那一头在父进程里关掉，子进程退出后读的一头才会读到结尾
  if (fds[0][0] >= 0) close(fds[0][0]);
  if (fds[1][1] >= 0) close(fds[1][1]);
  if (fds[2][1] >= 0) close(fds[2][1]);
  if (devnull >= 0) close(devnull);
  if (err) {
    if (fds[0][1] >= 0) close(fds[0][1]);
    if (fds[1][0] >= 0) close(fds[1][0]);
    if (fds[2][0] >= 0) close(fds[2][0]);
    lk_free(r);
    return -(int64_t)err;
  }
  int64_t deadline = timeout_ms > 0 ? lk_proc_now_ms() + timeout_ms : -1;
  if (capture) lk_proc_pump(r, fds[0][1], fds[1][0], fds[2][0], in, in_len, pid, deadline);
  int st = lk_proc_wait(pid, deadline, &r->timed_out);
  r->code = WIFEXITED(st) ? WEXITSTATUS(st) : 128 + (WIFSIGNALED(st) ? WTERMSIG(st) : 0);
  return (int64_t)(intptr_t)r;
}

__attribute__((used)) int64_t lark_proc_code(int64_t h) { return ((lk_proc_res*)(intptr_t)h)->code; }

// 是不是因为超时被结束的
__attribute__((used)) int lark_proc_timed_out(int64_t h) { return ((lk_proc_res*)(intptr_t)h)->timed_out; }

// k 为 0 是标准输出，1 是标准错误
__attribute__((used)) int64_t lark_proc_len(int64_t h, int k) { return (int64_t)((lk_proc_res*)(intptr_t)h)->len[k]; }

__attribute__((used)) void lark_proc_copy(int64_t h, int k, uint8_t* dst) {
  lk_proc_res* r = (lk_proc_res*)(intptr_t)h;
  if (r->len[k] > 0) memcpy(dst, r->buf[k], r->len[k]);
}

__attribute__((used)) void lark_proc_free(int64_t h) {
  lk_proc_res* r = (lk_proc_res*)(intptr_t)h;
  lk_free(r->buf[0]);
  lk_free(r->buf[1]);
  lk_free(r);
}

// ---------- 时区和程序路径（std/time、std/os 用 extern "c" 调用） ----------
#ifdef __APPLE__
#include <mach-o/dyld.h>
#endif
#include <limits.h>

int64_t lark_tz_offset(int64_t ms);
const char* lark_exe_path(void);

// 系统时区（TZ 环境变量或 /etc/localtime）在 ms 这一刻比 UTC 早多少分钟（东边为正，夏令时也算进去）
__attribute__((used)) int64_t lark_tz_offset(int64_t ms) {
  time_t t = (time_t)(ms >= 0 ? ms / 1000 : (ms - 999) / 1000);
  struct tm tm;
  if (!localtime_r(&t, &tm)) return 0;
  return (int64_t)tm.tm_gmtoff / 60;
}

// 当前程序的绝对路径（解析过符号链接）；查不到时是 ""。结果放在线程自己的缓冲区里，Lark 那边会马上复制
__attribute__((used)) const char* lark_exe_path(void) {
  static __thread char out[PATH_MAX + 1];
  char raw[PATH_MAX + 1];
  out[0] = 0;
#ifdef __APPLE__
  uint32_t size = sizeof raw;
  if (_NSGetExecutablePath(raw, &size) != 0) return out;
#else
  ssize_t n = readlink("/proc/self/exe", raw, PATH_MAX);
  if (n <= 0) return out;
  raw[n] = 0;
#endif
  if (!realpath(raw, out)) {
    strncpy(out, raw, PATH_MAX);
    out[PATH_MAX] = 0;
  }
  return out;
}

// ---------- 文件信息、权限、符号链接（std/os 的底层） ----------
// 返回字符串的函数：成功时以 + 开头，失败时是 "-errno"。结果放在线程自己的缓冲区里，Lark 那边会马上复制
const char* lark_stat_info(const char* path, int follow);
int lark_chmod(const char* path, int64_t mode);
const char* lark_read_link(const char* path);
int lark_symlink(const char* target, const char* link);
int lark_hard_link(const char* existing, const char* new_path);
int lark_set_mtime(const char* path, int64_t ms);

// "+种类 大小 修改时间 权限"：种类 1 普通文件、2 目录、3 符号链接（只有 follow 为 0 时）、4 其它；修改时间是 Unix 毫秒；权限是 st_mode 的低 12 位。
// follow 为 1 时符号链接按它指向的东西算（stat），为 0 时看链接本身（lstat）
__attribute__((used)) const char* lark_stat_info(const char* path, int follow) {
  static __thread char out[96];
  struct stat sb;
  if ((follow ? stat(path, &sb) : lstat(path, &sb)) != 0) {
    snprintf(out, sizeof out, "-%d", errno);
    return out;
  }
  int kind = S_ISREG(sb.st_mode) ? 1 : S_ISDIR(sb.st_mode) ? 2 : S_ISLNK(sb.st_mode) ? 3 : 4;
#ifdef __APPLE__
  struct timespec mt = sb.st_mtimespec;
#else
  struct timespec mt = sb.st_mtim;
#endif
  int64_t ms = (int64_t)mt.tv_sec * 1000 + mt.tv_nsec / 1000000;
  snprintf(out, sizeof out, "+%d %" PRId64 " %" PRId64 " %d", kind, (int64_t)sb.st_size, ms, (int)(sb.st_mode & 07777));
  return out;
}

// 成功时 0，失败时 errno
__attribute__((used)) int lark_chmod(const char* path, int64_t mode) {
  return chmod(path, (mode_t)(mode & 07777)) == 0 ? 0 : errno;
}

// "+链接里写的路径"（原样，不解析），失败时 "-errno"
__attribute__((used)) const char* lark_read_link(const char* path) {
  static __thread char out[PATH_MAX + 2];
  ssize_t n = readlink(path, out + 1, PATH_MAX);
  if (n < 0) {
    snprintf(out, sizeof out, "-%d", errno);
    return out;
  }
  out[0] = '+';
  out[n + 1] = 0;
  return out;
}

// 新建符号链接 link，内容是 target（target 不必存在）；成功时 0，失败时 errno
__attribute__((used)) int lark_symlink(const char* target, const char* link) {
  return symlink(target, link) == 0 ? 0 : errno;
}

// 硬链接：new_path 和 existing 是同一个文件
__attribute__((used)) int lark_hard_link(const char* existing, const char* new_path) {
  return link(existing, new_path) == 0 ? 0 : errno;
}

// 改修改时间（Unix 毫秒，可以是负数），访问时间不变；符号链接改的是它指向的文件
__attribute__((used)) int lark_set_mtime(const char* path, int64_t ms) {
  int64_t s = ms / 1000, r = ms % 1000;
  if (r < 0) { s -= 1; r += 1000; }
  struct timespec ts[2] = {{0, UTIME_OMIT}, {(time_t)s, (long)(r * 1000000)}};
  return utimensat(AT_FDCWD, path, ts, 0) == 0 ? 0 : errno;
}

// ---------- 信号（std/signal 的底层） ----------
// self-pipe：信号处理函数只往管道里写一个字节（信号编号），std/signal 从读的一头读。
// 处理函数里不加锁、不分配内存，只调用 write（异步信号安全）。读的一头是普通的管道，
// 任务读它的时候和读标准输入一样：没有数据就挂起，由事件循环叫醒，不占系统线程。
int lark_signal_watch(int sig);

static int lk_sig_pipe[2] = {-1, -1};
static pthread_once_t lk_sig_once = PTHREAD_ONCE_INIT;
static int lk_sig_err;

static void lk_sig_open(void) {
  if (pipe(lk_sig_pipe) != 0) { lk_sig_err = errno; return; }
  for (int k = 0; k < 2; k++) fcntl(lk_sig_pipe[k], F_SETFD, FD_CLOEXEC);
  // 写的一头不阻塞：一下子来很多信号、管道满了时丢掉，不让处理函数卡住
  fcntl(lk_sig_pipe[1], F_SETFL, fcntl(lk_sig_pipe[1], F_GETFL) | O_NONBLOCK);
}

static void lk_sig_on(int sig) {
  int saved = errno;
  unsigned char b = (unsigned char)sig;
  ssize_t n = write(lk_sig_pipe[1], &b, 1);
  (void)n;
  errno = saved;
}

// 从现在起 sig 不再按默认的方式处理，而是写进管道。返回读的一头的描述符，失败时是 -errno
__attribute__((used)) int lark_signal_watch(int sig) {
  pthread_once(&lk_sig_once, lk_sig_open);
  if (lk_sig_pipe[0] < 0) return -lk_sig_err;
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_handler = lk_sig_on;
  sa.sa_flags = SA_RESTART;
  sigemptyset(&sa.sa_mask);
  if (sigaction(sig, &sa, NULL) != 0) return -errno;
  return lk_sig_pipe[0];
}

// ---------- TCP（std/net 的底层） ----------
// 读用 lk_try_fd_read，关闭用 lk_try_fd_close；写用 lk_try_sock_write（对方关闭时不会收到 SIGPIPE 而退出）

// "动作 host:port：原因"
static lk_str lk_net_err(const char* what, lk_str host, int64_t port, const char* why) {
  char ps[32];
  snprintf(ps, sizeof ps, ":%" PRId64 "：", port);
  lk_str e = lk_str_new();
  lk_str_append_raw(&e, what, (int64_t)strlen(what));
  lk_str_append(&e, host);
  lk_str_append_raw(&e, ps, (int64_t)strlen(ps));
  lk_str_append_raw(&e, why, (int64_t)strlen(why));
  return e;
}

static lk_str lk_c_msg(const char* m) { return lk_str_from(m, (int64_t)strlen(m)); }

// 新的连接：exec 子进程时关掉，写给已关闭的连接时不发 SIGPIPE（macOS），小包不等待合并
static void lk_sock_setup(int fd) {
  int one = 1;
  fcntl(fd, F_SETFD, FD_CLOEXEC);
#ifdef SO_NOSIGPIPE
  setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof one);
#endif
  setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);
}

// host 为空串时监听所有地址（只用于 listen）
static struct addrinfo* lk_resolve(lk_str host, int64_t port, bool passive, lk_str* err) {
  if (port < 0 || port > 65535) { *err = lk_net_err("端口不对 ", host, port, "要在 0..65535 里"); return NULL; }
  struct addrinfo hints;
  memset(&hints, 0, sizeof hints);
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  if (passive) hints.ai_flags = AI_PASSIVE;
  char ps[16];
  snprintf(ps, sizeof ps, "%d", (int)port);
  const char* h = lk_str_len(host) == 0 ? NULL : lk_str_ptr(host);
  struct addrinfo* res = NULL;
  int rc = getaddrinfo(h, ps, &hints, &res);
  if (rc != 0) { *err = lk_net_err("无法解析 ", host, port, gai_strerror(rc)); return NULL; }
  return res;
}

static int64_t __attribute__((unused)) lk_try_tcp_connect(lk_str host, int64_t port, lk_str* err) {
  struct addrinfo* res = lk_resolve(host, port, false, err);
  if (!res) return -1;
  int fd = -1, why = 0;
  for (struct addrinfo* a = res; a; a = a->ai_next) {
    fd = socket(a->ai_family, a->ai_socktype, a->ai_protocol);
    if (fd < 0) { why = errno; continue; }
    if (connect(fd, a->ai_addr, a->ai_addrlen) == 0) break;
    why = errno;
    close(fd);
    fd = -1;
  }
  freeaddrinfo(res);
  if (fd < 0) { *err = lk_net_err("无法连接 ", host, port, strerror(why)); return -1; }
  lk_sock_setup(fd);
  return fd;
}

static int64_t __attribute__((unused)) lk_try_tcp_listen(lk_str host, int64_t port, lk_str* err) {
  struct addrinfo* res = lk_resolve(host, port, true, err);
  if (!res) return -1;
  int fd = -1, why = 0;
  for (struct addrinfo* a = res; a; a = a->ai_next) {
    fd = socket(a->ai_family, a->ai_socktype, a->ai_protocol);
    if (fd < 0) { why = errno; continue; }
    int one = 1;
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    if (bind(fd, a->ai_addr, a->ai_addrlen) == 0 && listen(fd, 128) == 0) break;
    why = errno;
    close(fd);
    fd = -1;
  }
  freeaddrinfo(res);
  if (fd < 0) { *err = lk_net_err("无法监听 ", host, port, strerror(why)); return -1; }
  fcntl(fd, F_SETFD, FD_CLOEXEC);
  return fd;
}

static int64_t __attribute__((unused)) lk_try_tcp_accept(int64_t lfd, lk_str* err) {
  int fd;
  int64_t dl = -2;
  // 调度器启动以后 Listener 设成不阻塞：先试 accept，没有连接再等（事件循环是边沿触发，先等再 accept
  // 会漏掉一起到的几个连接）。macOS 上 accept 出来的连接也跟着不阻塞，启动以后的读写本来就按不阻塞处理
  if (lk_started) lk_fd_nonblock((int)lfd);
  for (;;) {
    fd = accept((int)lfd, NULL, NULL);
    if (fd >= 0) break;
    if (errno == EINTR) continue;
    if (lk_started && (errno == EAGAIN || errno == EWOULDBLOCK || errno == ECONNABORTED)) {
      // 设了超时（net 的 Listener.set_timeout_ms）时等到点就返回“：超时”，http.serve 靠它定时看看是不是该停了
      if (dl == -2) dl = lk_fd_deadline((int)lfd);
      if (!lk_fd_wait((int)lfd, false, dl)) { errno = EAGAIN; break; }
      continue;
    }
    break;
  }
  if (fd < 0) { *err = lk_fd_err_t("accept 失败，文件描述符 ", lfd); return -1; }
  lk_sock_setup(fd);
  return fd;
}

// 本地端口（listen 时给 0 让系统挑一个空闲的端口，再用它查）
static int64_t __attribute__((unused)) lk_try_sock_port(int64_t fd, lk_str* err) {
  struct sockaddr_storage ss;
  socklen_t n = sizeof ss;
  if (getsockname((int)fd, (struct sockaddr*)&ss, &n) != 0) { *err = lk_fd_err("查不到端口，文件描述符 ", fd); return -1; }
  if (ss.ss_family == AF_INET) return ntohs(((struct sockaddr_in*)&ss)->sin_port);
  if (ss.ss_family == AF_INET6) return ntohs(((struct sockaddr_in6*)&ss)->sin6_port);
  *err = lk_c_msg("查不到端口：不是 TCP 连接");
  return -1;
}

#ifdef MSG_NOSIGNAL
#define LK_SEND_FLAGS MSG_NOSIGNAL
#else
#define LK_SEND_FLAGS 0
#endif

static int64_t __attribute__((unused)) lk_try_sock_write(int64_t fd, lk_str s, lk_str* err) {
  const char* p = lk_str_ptr(s);
  int64_t left = lk_str_len(s);
  int64_t dl = -2;
  while (left > 0) {
    ssize_t n = send((int)fd, p, (size_t)left, LK_SEND_FLAGS | (lk_started ? MSG_DONTWAIT : 0));
    if (n < 0 && errno == EINTR) continue;
    if (n < 0 && lk_started && (errno == EAGAIN || errno == EWOULDBLOCK)) {
      // 发送缓冲区满了：等它可写
      if (dl == -2) dl = lk_fd_deadline((int)fd);
      if (lk_fd_wait((int)fd, true, dl)) continue;
      errno = EAGAIN;
    }
    if (n < 0) { *err = lk_fd_err_t("发送失败，文件描述符 ", fd); return 0; }
    p += n;
    left -= n;
  }
  return 0;
}

// 读和写的超时（毫秒，0 表示不超时）；超时后读写返回错误
static int64_t __attribute__((unused)) lk_try_sock_timeout(int64_t fd, int64_t ms, lk_str* err) {
  if (ms < 0) { *err = lk_c_msg("超时不能是负数"); return 0; }
  lk_fd_set_timeout((int)fd, ms);
  struct timeval tv;
  tv.tv_sec = (time_t)(ms / 1000);
  tv.tv_usec = (int)((ms % 1000) * 1000);
  if (setsockopt((int)fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv) != 0 ||
      setsockopt((int)fd, SOL_SOCKET, SO_SNDTIMEO, &tv, sizeof tv) != 0) {
    *err = lk_fd_err("设置超时失败，文件描述符 ", fd);
  }
  return 0;
}

// ---------- UDP、Unix 域套接字、DNS（std/net 用 extern "c" 调用，所以不是 static） ----------
// 成功时返回 >= 0，失败时 -1，原因用 lark_net_error() 取（每个线程一份）。收数据报时没有数据就和 TCP 的读一样挂起任务；
// 挂起以后可能在别的线程上醒来，所以原因、对方地址都在最后一次挂起之后才写，调用方紧接着取（中间没有会挂起的调用）。
// 连接、解析（getaddrinfo）和 net.connect 一样，等的时候占着一个系统线程。
#include <arpa/inet.h>
#include <sys/un.h>
const char* lark_net_error(void);
int64_t lark_udp_bind(const char* host, int64_t port);
int64_t lark_udp_send(int64_t fd, const char* host, int64_t port, uint8_t* data, int64_t n);
int64_t lark_udp_recv(int64_t fd, uint8_t* buf, int64_t cap);
const char* lark_udp_peer(void);
int64_t lark_unix_listen(const char* path);
int64_t lark_unix_connect(const char* path);
const char* lark_lookup(const char* host);

static __thread char lk_net_msg[512];
static __thread char lk_udp_from[INET6_ADDRSTRLEN + 16];

// "动作对象：原因"，返回 -1
static int64_t lk_net_fail(const char* what, const char* obj, const char* why) {
  snprintf(lk_net_msg, sizeof lk_net_msg, "%s%s：%s", what, obj, why);
  return -1;
}

__attribute__((used)) const char* lark_net_error(void) { return lk_net_msg; }

// 地址写成文字：IPv4 "1.2.3.4"，IPv6 "::1"；port 不为 NULL 时顺便取端口
static void lk_addr_text(const struct sockaddr_storage* ss, char* out, size_t n, int* port) {
  out[0] = 0;
  if (ss->ss_family == AF_INET) {
    const struct sockaddr_in* a = (const struct sockaddr_in*)ss;
    inet_ntop(AF_INET, &a->sin_addr, out, (socklen_t)n);
    if (port) *port = ntohs(a->sin_port);
  } else if (ss->ss_family == AF_INET6) {
    const struct sockaddr_in6* a = (const struct sockaddr_in6*)ss;
    if (IN6_IS_ADDR_V4MAPPED(&a->sin6_addr)) {
      // IPv6 的套接字收到的 IPv4 地址：写成 1.2.3.4，回信时 lark_udp_send 再换回来
      inet_ntop(AF_INET, &a->sin6_addr.s6_addr[12], out, (socklen_t)n);
    } else {
      inet_ntop(AF_INET6, &a->sin6_addr, out, (socklen_t)n);
    }
    if (port) *port = ntohs(a->sin6_port);
  }
}

static struct addrinfo* lk_udp_resolve(const char* host, int64_t port, bool passive, const char* what) {
  char obj[320];
  snprintf(obj, sizeof obj, "%s:%" PRId64, host, port);
  if (port < 0 || port > 65535) { lk_net_fail(what, obj, "端口要在 0..65535 里"); return NULL; }
  struct addrinfo hints;
  memset(&hints, 0, sizeof hints);
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_DGRAM;
  if (passive) hints.ai_flags = AI_PASSIVE;
  char ps[16];
  snprintf(ps, sizeof ps, "%d", (int)port);
  struct addrinfo* res = NULL;
  int rc = getaddrinfo(host[0] ? host : NULL, ps, &hints, &res);
  if (rc != 0) { lk_net_fail("无法解析 ", obj, gai_strerror(rc)); return NULL; }
  return res;
}

// 绑定一个 UDP 端口；host 为空串时所有地址，port 为 0 时由系统挑
__attribute__((used)) int64_t lark_udp_bind(const char* host, int64_t port) {
  struct addrinfo* res = lk_udp_resolve(host, port, true, "无法监听 UDP ");
  if (!res) return -1;
  int fd = -1, why = 0;
  for (struct addrinfo* a = res; a; a = a->ai_next) {
    fd = socket(a->ai_family, a->ai_socktype, a->ai_protocol);
    if (fd < 0) { why = errno; continue; }
    if (bind(fd, a->ai_addr, a->ai_addrlen) == 0) break;
    why = errno;
    close(fd);
    fd = -1;
  }
  freeaddrinfo(res);
  char obj[320];
  snprintf(obj, sizeof obj, "%s:%" PRId64, host, port);
  if (fd < 0) return lk_net_fail("无法监听 UDP ", obj, strerror(why));
  fcntl(fd, F_SETFD, FD_CLOEXEC);
  return fd;
}

// 发一个数据报给 host:port（每次都解析 host；数字地址不查 DNS）
__attribute__((used)) int64_t lark_udp_send(int64_t fd, const char* host, int64_t port, uint8_t* data, int64_t n) {
  char obj[320];
  snprintf(obj, sizeof obj, "%s:%" PRId64, host, port);
  if (!host[0]) return lk_net_fail("无法发送到 ", obj, "没有给地址");
  struct addrinfo* res = lk_udp_resolve(host, port, false, "无法发送到 ");
  if (!res) return -1;
  // 选一个和套接字同一类（IPv4 / IPv6）的地址。IPv6 的套接字（监听 "" 时常是这种）发给 IPv4 地址时，
  // 换成 IPv4 映射的地址 ::ffff:a.b.c.d（系统默认没有开 IPV6_V6ONLY，所以发得出去）
  struct sockaddr_storage me;
  socklen_t ml = sizeof me;
  int fam = getsockname((int)fd, (struct sockaddr*)&me, &ml) == 0 ? me.ss_family : AF_UNSPEC;
  struct sockaddr_storage to;
  socklen_t tl = 0;
  for (struct addrinfo* a = res; a && tl == 0; a = a->ai_next) {
    if (a->ai_family == fam) {
      memcpy(&to, a->ai_addr, a->ai_addrlen);
      tl = a->ai_addrlen;
    }
  }
  for (struct addrinfo* a = res; a && tl == 0 && fam == AF_INET6; a = a->ai_next) {
    if (a->ai_family != AF_INET) continue;
    const struct sockaddr_in* v4 = (const struct sockaddr_in*)a->ai_addr;
    struct sockaddr_in6* v6 = (struct sockaddr_in6*)&to;
    memset(v6, 0, sizeof *v6);
    v6->sin6_family = AF_INET6;
    v6->sin6_port = v4->sin_port;
    v6->sin6_addr.s6_addr[10] = 0xff;
    v6->sin6_addr.s6_addr[11] = 0xff;
    memcpy(&v6->sin6_addr.s6_addr[12], &v4->sin_addr, 4);
    tl = sizeof *v6;
  }
  freeaddrinfo(res);
  if (tl == 0) return lk_net_fail("无法发送到 ", obj, "这个套接字是 IPv4 的，地址只有 IPv6 的");
  ssize_t r;
  int64_t dl = -2;
  for (;;) {
    r = sendto((int)fd, data, (size_t)n, LK_SEND_FLAGS | (lk_started ? MSG_DONTWAIT : 0), (struct sockaddr*)&to, tl);
    if (r >= 0) break;
    if (errno == EINTR) continue;
    if (lk_started && (errno == EAGAIN || errno == EWOULDBLOCK)) {
      if (dl == -2) dl = lk_fd_deadline((int)fd);
      if (lk_fd_wait((int)fd, true, dl)) continue;
      errno = EAGAIN;
    }
    break;
  }
  int why = errno;
  if (r < 0) return lk_net_fail("无法发送到 ", obj, why == EAGAIN ? "超时" : strerror(why));
  return r;
}

// 收一个数据报，最多 cap 个字节写进 buf，多出来的丢掉；返回收到的字节数。发送方是 lark_udp_peer() 的 "地址 端口"
__attribute__((used)) int64_t lark_udp_recv(int64_t fd, uint8_t* buf, int64_t cap) {
  struct sockaddr_storage ss;
  socklen_t sl;
  ssize_t n;
  int64_t dl = -2;
  for (;;) {
    sl = sizeof ss;
    n = recvfrom((int)fd, buf, (size_t)cap, lk_started ? MSG_DONTWAIT : 0, (struct sockaddr*)&ss, &sl);
    if (n >= 0) break;
    if (errno == EINTR) continue;
    if (lk_started && (errno == EAGAIN || errno == EWOULDBLOCK)) {
      if (dl == -2) dl = lk_fd_deadline((int)fd);
      if (lk_fd_wait((int)fd, false, dl)) continue;
      errno = EAGAIN;
    }
    break;
  }
  if (n < 0) {
    int why = errno;
    char obj[32];
    snprintf(obj, sizeof obj, "%" PRId64, fd);
    return lk_net_fail("接收失败，文件描述符 ", obj, (why == EAGAIN || why == EWOULDBLOCK) ? "超时" : strerror(why));
  }
  char a[INET6_ADDRSTRLEN];
  int port = 0;
  lk_addr_text(&ss, a, sizeof a, &port);
  snprintf(lk_udp_from, sizeof lk_udp_from, "%s %d", a, port);
  return n;
}

__attribute__((used)) const char* lark_udp_peer(void) { return lk_udp_from; }

static int64_t lk_unix_addr(const char* path, struct sockaddr_un* sa, const char* what) {
  memset(sa, 0, sizeof *sa);
  sa->sun_family = AF_UNIX;
  if (!path[0]) return lk_net_fail(what, "\"\"", "路径是空的");
  if (strlen(path) >= sizeof sa->sun_path) {
    char why[64];
    snprintf(why, sizeof why, "路径太长（最多 %d 个字节）", (int)sizeof sa->sun_path - 1);
    return lk_net_fail(what, path, why);
  }
  strcpy(sa->sun_path, path);
  return 0;
}

// 在 path 上监听；path 已经存在时失败（不替调用方删文件）
__attribute__((used)) int64_t lark_unix_listen(const char* path) {
  struct sockaddr_un sa;
  if (lk_unix_addr(path, &sa, "无法监听 ") < 0) return -1;
  int fd = socket(AF_UNIX, SOCK_STREAM, 0);
  if (fd < 0) return lk_net_fail("无法监听 ", path, strerror(errno));
  if (bind(fd, (struct sockaddr*)&sa, sizeof sa) != 0 || listen(fd, 128) != 0) {
    int why = errno;
    close(fd);
    return lk_net_fail("无法监听 ", path, strerror(why));
  }
  fcntl(fd, F_SETFD, FD_CLOEXEC);
  return fd;
}

__attribute__((used)) int64_t lark_unix_connect(const char* path) {
  struct sockaddr_un sa;
  if (lk_unix_addr(path, &sa, "无法连接 ") < 0) return -1;
  int fd = socket(AF_UNIX, SOCK_STREAM, 0);
  if (fd < 0) return lk_net_fail("无法连接 ", path, strerror(errno));
  int r;
  do { r = connect(fd, (struct sockaddr*)&sa, sizeof sa); } while (r != 0 && errno == EINTR);
  if (r != 0) {
    int why = errno;
    close(fd);
    return lk_net_fail("无法连接 ", path, strerror(why));
  }
  lk_sock_setup(fd);
  return fd;
}

// host 的所有地址，一行一个，按 getaddrinfo 给的顺序、去掉重复的；前面一个字节 '+'。失败时是 "-原因"
__attribute__((used)) const char* lark_lookup(const char* host) {
  static __thread char out[4096];
  struct addrinfo hints;
  memset(&hints, 0, sizeof hints);
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  struct addrinfo* res = NULL;
  int rc = getaddrinfo(host, NULL, &hints, &res);
  if (rc != 0) {
    snprintf(out, sizeof out, "-无法解析 %s：%s", host, gai_strerror(rc));
    return out;
  }
  size_t len = 1;
  out[0] = '+';
  out[1] = 0;
  for (struct addrinfo* a = res; a; a = a->ai_next) {
    struct sockaddr_storage ss;
    memset(&ss, 0, sizeof ss);
    memcpy(&ss, a->ai_addr, a->ai_addrlen < sizeof ss ? a->ai_addrlen : sizeof ss);
    char t[INET6_ADDRSTRLEN];
    lk_addr_text(&ss, t, sizeof t, NULL);
    if (!t[0]) continue;
    // 去重：整行比较
    char line[INET6_ADDRSTRLEN + 2];
    snprintf(line, sizeof line, "\n%s\n", t);
    char probe[sizeof out + 2];
    snprintf(probe, sizeof probe, "\n%s\n", out + 1);
    if (strstr(probe, line)) continue;
    size_t tl = strlen(t);
    if (len + tl + 2 >= sizeof out) break;
    if (len > 1) out[len++] = '\n';
    memcpy(out + len, t, tl);
    len += tl;
    out[len] = 0;
  }
  freeaddrinfo(res);
  return out;
}

// 删除文件或空目录
static int64_t __attribute__((unused)) lk_try_remove(lk_str path, lk_str* err) {
  if (remove(lk_str_ptr(path)) != 0) *err = lk_os_err("无法删除 ", path);
  return 0;
}

static int64_t __attribute__((unused)) lk_try_mkdir(lk_str path, lk_str* err) {
  if (mkdir(lk_str_ptr(path), 0777) != 0) *err = lk_os_err("无法创建目录 ", path);
  return 0;
}

static int64_t __attribute__((unused)) lk_try_rename(lk_str from, lk_str to, lk_str* err) {
  if (rename(lk_str_ptr(from), lk_str_ptr(to)) != 0) *err = lk_os_err("无法重命名 ", from);
  return 0;
}

static lk_str __attribute__((unused)) lk_try_cwd(lk_str* err) {
  char buf[4096];
  if (!getcwd(buf, sizeof buf)) { *err = lk_os_err("无法取得当前目录", NULL); return NULL; }
  return lk_str_from(buf, (int64_t)strlen(buf));
}

static lk_str __attribute__((unused)) lk_try_getenv(lk_str name, lk_str* err) {
  const char* v = getenv(lk_str_ptr(name));
  if (!v) {
    lk_str e = lk_str_new();
    lk_str_append_raw(&e, "没有环境变量 ", (int64_t)strlen("没有环境变量 "));
    lk_str_append(&e, name);
    *err = e;
    return NULL;
  }
  return lk_str_from(v, (int64_t)strlen(v));
}

// 用 sh 运行命令，返回它的标准输出（标准错误照常显示）；退出码不为 0 也算失败
static lk_str __attribute__((unused)) lk_try_capture(lk_str cmd, lk_str* err) {
  fflush(stdout);
  FILE* p = popen(lk_str_ptr(cmd), "r");
  if (!p) { *err = lk_os_err("无法运行命令 ", cmd); return NULL; }
  lk_str out = lk_str_new();
  char buf[4096];
  size_t n;
  while ((n = fread(buf, 1, sizeof buf, p)) > 0) lk_str_append_raw(&out, buf, (int64_t)n);
  int st = pclose(p);
  int code = WIFEXITED(st) ? WEXITSTATUS(st) : 128 + (WIFSIGNALED(st) ? WTERMSIG(st) : 0);
  if (code != 0) {
    char msg[64];
    snprintf(msg, sizeof msg, "（退出码 %d）", code);
    lk_str e = lk_str_new();
    lk_str_append_raw(&e, "命令失败：", (int64_t)strlen("命令失败："));
    lk_str_append(&e, cmd);
    lk_str_append_raw(&e, msg, (int64_t)strlen(msg));
    lk_drop_s(&out);
    *err = e;
    return NULL;
  }
  return out;
}

// 运行命令，返回它的退出码（被信号终止时为 128 + 信号编号）；system 返回的是原始的等待状态
static int64_t __attribute__((unused)) lk_run(lk_str cmd) {
  fflush(stdout);
  int st = system(lk_str_ptr(cmd));
  if (st == -1) return -1;
  return WIFEXITED(st) ? WEXITSTATUS(st) : 128 + (WIFSIGNALED(st) ? WTERMSIG(st) : 0);
}

#endif  // 可选部分（一）

// 从 1970-01-01 起的毫秒数（墙上时间）
static int64_t __attribute__((unused)) lk_now_ms(void) { return lark_plat_now_ns() / 1000000; }

// 从 1970-01-01 起的纳秒数（墙上时间，可能被系统调整）
static int64_t __attribute__((unused)) lk_now_ns(void) { return lark_plat_now_ns(); }

// 单调时钟的纳秒数：只增不减，起点不确定，只用来量时间间隔
static int64_t __attribute__((unused)) lk_mono_ns(void) { return lark_plat_mono_ns(); }

static int lk_argc_;
static char** lk_argv_;

#ifdef LK_CORE
// 栈溢出保护（保护页加信号处理）在可选部分里：只带核心时栈溢出由系统直接报段错误
static void lk_guard_install(char* stack_hi) { (void)stack_hi; }
#else
static void lk_guard_install(char* stack_hi);
#endif

static void lk_init(int argc, char** argv) {
  char here;
  lk_guard_install(&here);
#if !defined(LK_NOTRACE) && !defined(LK_CORE)
  lk_slot_ = &lk_main_top;
#endif
  lk_argc_ = argc;
  lk_argv_ = argv;
}

static int64_t __attribute__((unused)) lk_argc(void) { return lk_argc_; }

static lk_str __attribute__((unused)) lk_argv(int64_t i) {
  return lk_str_from(lk_argv_[i], (int64_t)strlen(lk_argv_[i]));
}

// ---------- 测试：lark1 --test 生成的 main 调用 lk_run_tests ----------
// 要 fork、pipe 和 stdio，所以 LK_BARE 时没有（测试在有操作系统的机器上跑）
#ifndef LK_BARE
// 每个测试在子进程里运行，panic、exit 和崩溃都不会影响别的测试；子进程的输出先收起来，失败时才缩进打印。
// filter 不为 NULL 时只运行名字里含有它的测试。有测试失败时返回 1。
typedef void (*lk_test_fn)(void);

static int __attribute__((unused)) lk_run_tests(int n, const char** names, lk_test_fn const* fns, const char* filter) {
  int ran = 0, failed = 0;
  for (int i = 0; i < n; i++) {
    if (filter && !strstr(names[i], filter)) continue;
    ran++;
    fflush(stdout);
    fflush(stderr);
    int fd[2];
    if (pipe(fd) != 0) lk_panic_c("测试：创建管道失败");
    pid_t pid = fork();
    if (pid < 0) lk_panic_c("测试：创建子进程失败");
    if (pid == 0) {
      close(fd[0]);
      dup2(fd[1], 1);
      dup2(fd[1], 2);
      close(fd[1]);
      fns[i]();
      fflush(stdout);
      _exit(0);
    }
    close(fd[1]);
    char* buf = NULL;
    size_t len = 0, cap = 0;
    char chunk[4096];
    ssize_t k;
    while ((k = read(fd[0], chunk, sizeof chunk)) > 0) {
      if (len + (size_t)k > cap) {
        cap = (len + (size_t)k) * 2;
        buf = lk_realloc(buf, cap);
      }
      memcpy(buf + len, chunk, (size_t)k);
      len += (size_t)k;
    }
    close(fd[0]);
    int st = 0;
    waitpid(pid, &st, 0);
    if (WIFEXITED(st) && WEXITSTATUS(st) == 0) {
      printf("通过  %s\n", names[i]);
    } else {
      failed++;
      if (WIFSIGNALED(st)) {
        printf("失败  %s（被信号 %d 终止）\n", names[i], WTERMSIG(st));
      } else if (WEXITSTATUS(st) == 101) {
        printf("失败  %s\n", names[i]);     // panic：原因在下面的输出里
      } else {
        printf("失败  %s（退出码 %d）\n", names[i], WEXITSTATUS(st));
      }
      int bol = 1;
      for (size_t j = 0; j < len; j++) {
        if (bol) fputs("    ", stdout);
        fputc(buf[j], stdout);
        bol = buf[j] == '\n';
      }
      if (!bol) fputc('\n', stdout);
    }
    lk_free(buf);
  }
  if (filter && ran == 0) printf("没有名字里含有“%s”的测试\n", filter);
  printf("%d 项测试：%d 项通过，%d 项失败\n", ran, ran - failed, failed);
  return failed > 0 ? 1 : 0;
}
#endif

#ifndef LK_CORE  // 可选部分（二）：任务、调度器、事件循环、定时器、栈溢出保护、Mutex、Chan

// ---------- 任务与调度器（stage 4，设计见 design/stage4-tasks.md）----------
// spawn 出来的是任务：有自己的栈的协程，由调度器放到 LARK_PROCS 个工作线程（默认是 CPU 核数）上运行。
// 任务只在等待的地方让出：通道的 recv / select、scope 块尾、sleep。不抢占。
// 第一次 spawn 时才启动调度器：当前正在运行的代码成为“主任务”，继续用原来的栈；没有用并发的程序什么都不创建。

// 栈切换：lk_swap_ctx(&旧的栈指针, 新的栈指针) 把被调用者保存的寄存器压到当前栈上、记下栈指针，
// 换到新栈，弹出那边的寄存器后返回，也就是回到那边当初调用 lk_swap_ctx 的地方。
// 新任务的栈上预先放好一组“寄存器”，返回地址是 lk_task_boot，它用其中两个寄存器里的参数和函数开始运行。
void lk_swap_ctx(void** save_sp, void* new_sp);

// ThreadSanitizer 要知道栈在什么时候换了（fiber）：不告诉它时，它把同一个线程上的几个任务当成一个，
// 报出假的数据竞争，还会在自己记录调用栈时出错。每个任务和每个调度循环各有一个 fiber，切换前先告诉它要换到哪个。
// 没加 -fsanitize=thread 时这些都是空的。
// AddressSanitizer 的 __sanitizer_start_switch_fiber 还没有加：它要每块栈的准确范围（包括主线程原来的栈），
// 现在不加也能正常检查（make asan、ASan 下跑全部测试都是干净的），只是栈上越界的检查在任务的栈上不够精确
#if defined(__has_feature)
#if __has_feature(thread_sanitizer)
#define LK_TSAN 1
#endif
#endif
#ifdef __SANITIZE_THREAD__
#define LK_TSAN 1
#endif
#ifdef LK_TSAN
void* __tsan_get_current_fiber(void);
void* __tsan_create_fiber(unsigned flags);
void __tsan_destroy_fiber(void* fiber);
void __tsan_switch_to_fiber(void* fiber, unsigned flags);
#define lk_fib_current() __tsan_get_current_fiber()
#define lk_fib_new() __tsan_create_fiber(0)
#define lk_fib_free(f) __tsan_destroy_fiber(f)
#define lk_fib_switch(f) __tsan_switch_to_fiber((f), 0)
// 挂起时锁的交接：任务在自己的 fiber 上加锁，切到调度循环以后由那边解锁（见 lk_park）。
// ThreadSanitizer 按 fiber 记录谁拿着锁：别的 fiber 解锁时它不认，锁保护的读写就都被报成数据竞争。
// 所以切换前在加锁的 fiber 上告诉它“解开了”（lk_tsan_give），调度循环真正解锁前告诉它“这边拿到了”（lk_tsan_take）
void __tsan_mutex_pre_lock(void* addr, unsigned flags);
void __tsan_mutex_post_lock(void* addr, unsigned flags, int recursion);
int __tsan_mutex_pre_unlock(void* addr, unsigned flags);
void __tsan_mutex_post_unlock(void* addr, unsigned flags);
#define lk_tsan_give(mu) do { __tsan_mutex_pre_unlock((mu), 0); __tsan_mutex_post_unlock((mu), 0); } while (0)
#define lk_tsan_take(mu) do { __tsan_mutex_pre_lock((mu), 0); __tsan_mutex_post_lock((mu), 0, 0); } while (0)
#else
#define lk_fib_current() NULL
#define lk_fib_new() NULL
#define lk_fib_free(f) ((void)(f))
#define lk_fib_switch(f) ((void)(f))
#define lk_tsan_give(mu) ((void)(mu))
#define lk_tsan_take(mu) ((void)(mu))
#endif
void lk_task_boot(void);

#if defined(__APPLE__)
#define LK_SYM(x) "_" #x
#else
#define LK_SYM(x) #x
#endif

#if defined(__aarch64__)
// x19–x28、x29（帧指针）、x30（返回地址）、d8–d15，共 176 字节。x18 是平台保留的，不动。
// 新任务：x19 = 参数，x20 = 函数，x30 = lk_task_boot
#define LK_CTX_SIZE 176
#define LK_CTX_ARG 0
#define LK_CTX_FN 1
#define LK_CTX_RET 11
__asm__(
  ".text\n.p2align 2\n.globl " LK_SYM(lk_swap_ctx) "\n" LK_SYM(lk_swap_ctx) ":\n"
  "  sub sp, sp, #176\n"
  "  stp x19, x20, [sp, #0]\n  stp x21, x22, [sp, #16]\n  stp x23, x24, [sp, #32]\n"
  "  stp x25, x26, [sp, #48]\n  stp x27, x28, [sp, #64]\n  stp x29, x30, [sp, #80]\n"
  "  stp d8, d9, [sp, #96]\n  stp d10, d11, [sp, #112]\n  stp d12, d13, [sp, #128]\n  stp d14, d15, [sp, #144]\n"
  "  mov x2, sp\n  str x2, [x0]\n  mov sp, x1\n"
  "  ldp x19, x20, [sp, #0]\n  ldp x21, x22, [sp, #16]\n  ldp x23, x24, [sp, #32]\n"
  "  ldp x25, x26, [sp, #48]\n  ldp x27, x28, [sp, #64]\n  ldp x29, x30, [sp, #80]\n"
  "  ldp d8, d9, [sp, #96]\n  ldp d10, d11, [sp, #112]\n  ldp d12, d13, [sp, #128]\n  ldp d14, d15, [sp, #144]\n"
  "  add sp, sp, #176\n  ret\n"
  ".globl " LK_SYM(lk_task_boot) "\n" LK_SYM(lk_task_boot) ":\n"
  "  mov x0, x19\n  mov x29, #0\n  blr x20\n  brk #0\n");
#elif defined(__x86_64__)
// rbp rbx r12–r15 和返回地址，共 56 字节。新任务：r12 = 参数，r13 = 函数，返回地址 = lk_task_boot
// （弹出的顺序是 r15 r14 r13 r12 rbx rbp，所以 r13 在第 2 格、r12 在第 3 格）
#define LK_CTX_SIZE 56
#define LK_CTX_ARG 3
#define LK_CTX_FN 2
#define LK_CTX_RET 6
__asm__(
  ".text\n.p2align 4\n.globl " LK_SYM(lk_swap_ctx) "\n" LK_SYM(lk_swap_ctx) ":\n"
  "  pushq %rbp\n  pushq %rbx\n  pushq %r12\n  pushq %r13\n  pushq %r14\n  pushq %r15\n"
  "  movq %rsp, (%rdi)\n  movq %rsi, %rsp\n"
  "  popq %r15\n  popq %r14\n  popq %r13\n  popq %r12\n  popq %rbx\n  popq %rbp\n"
  "  ret\n"
  ".globl " LK_SYM(lk_task_boot) "\n" LK_SYM(lk_task_boot) ":\n"
  "  movq %r12, %rdi\n  xorl %ebp, %ebp\n  callq *%r13\n  ud2\n");
#else
#error "Lark 的任务切换只支持 arm64 和 x86_64"
#endif

// 在栈顶 top（16 字节对齐）下面放好新任务的初始“寄存器”，返回给 lk_swap_ctx 用的栈指针
static void* lk_ctx_init(char* top, void (*fn)(void*), void* arg) {
  void** sp = (void**)(top - LK_CTX_SIZE);
  memset(sp, 0, LK_CTX_SIZE);
  sp[LK_CTX_ARG] = arg;
  sp[LK_CTX_FN] = (void*)fn;
  sp[LK_CTX_RET] = (void*)lk_task_boot;
  return sp;
}

// 任务的栈：mmap 保留 LK_STACK 字节，最下面一页不可访问（保护页），只有用到的页才占内存。
// 结束的任务的栈放回池里（最多 64 块），池由调度器的锁保护。
#define LK_STACK ((size_t)1 << 20)
#define LK_STACK_POOL 64

static char* lk_stack_new(size_t size) {
  size_t page = (size_t)sysconf(_SC_PAGESIZE);
  char* p = (char*)mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
  if (p == MAP_FAILED) lk_panic_c("内存不足：无法分配任务的栈");
  mprotect(p, page, PROT_NONE);
  return p;
}

typedef struct lk_task {
  void* sp;                 // 挂起时的栈指针
  void* (*fn)(void*);       // spawn 生成的入口，参数块由它释放
  void* arg;
  char* stack;              // 主任务是 NULL（用进程原来的栈）
  void* top;                // 调用栈信息的链头（lk_frame*）
  void** topp;              // 指向链头：主任务指向 lk_main_top，别的任务指向自己的 top
  struct lk_scope* scope;
  struct lk_task* next;     // 运行队列里的下一个，也用来把一批要叫醒的任务串起来
  int64_t wait;             // 正在等待时是这次等待的编号，叫醒它的一方用 CAS 改成 0，抢到的才算数
  int64_t gen;              // 上一次等待的编号
  int fired;                // 怎么醒的：>= 0 是 select 的第几个通道送来了值，-1 到时间了，-3 有通道的持有者放手了
  int64_t hidx;             // 在定时器堆里的位置加一，0 表示不在堆里（以下三项由那个堆的锁保护）
  int64_t tat;              // 定时器的到期时间
  int64_t ttok;             // 定时器属于哪次等待
  struct lk_theap* theap;   // 定时器在哪个堆里，NULL 表示不在（在那个堆的锁里改，可以原子地读）
  void* fib;                // ThreadSanitizer 的 fiber（见 lk_fib_switch），没加 -fsanitize=thread 时是 NULL
} lk_task;

// 定时器堆：按 tat 排的最小堆（见“定时器堆”）
typedef struct lk_theap {
  pthread_mutex_t mu;
  lk_task** th;
  int64_t n, cap;
  int64_t first;            // 最早的到期时间，没有是 INT64_MAX（原子地读写）
} lk_theap;

typedef struct lk_scope {
  int64_t live;             // 还没结束的任务数（调度器的锁保护）
  lk_task* waiter;          // 在块尾等着的任务
} lk_scope;

typedef struct lk_worker {
  pthread_t th;
  void* sp;                 // 本线程调度循环的栈指针
  void* fib;                // 调度循环的 ThreadSanitizer fiber
  lk_task* cur;             // 正在运行的任务
  lk_task* runnext;         // “下一个”位置（原子地交换）：本线程上的任务叫醒的任务放在这里，接着运行
  lk_task* rn_seen;         // 看守线程上次看到的 runnext，连着两次是同一个就拿走（防止它一直等着）
  lk_task* dead;            // 刚结束的任务，切回调度循环以后释放
  void (*after)(void*);     // 任务挂起、切回调度循环以后要做的事（一般是解锁）
  void* after_arg;
  uint64_t tick;
  pthread_mutex_t qmu;      // 本线程的队列（qh、qt、qn）的锁，偷的线程也要拿它
  lk_task* qh;
  lk_task* qt;
  int64_t qn;               // 队列长度：在 qmu 里原子地改，不拿锁时原子地读（是 0 就不用拿锁）
  lk_theap tm;              // 本线程的定时器堆
} lk_worker;

// 锁不会嵌套着反过来拿（顺序：通道 → 定时器堆；调度器的锁、各线程队列的锁不和别的嵌套）。fd 表不加锁（见“事件循环”）：
// - 调度器的锁：全局运行队列、栈池、scope 的计数、空闲线程的状态
// - 每个线程的定时器堆各有一把锁
static pthread_mutex_t lk_sched_mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t lk_sched_cv = PTHREAD_COND_INITIALIZER;
static bool lk_started;
static lk_worker* lk_ws;
static int lk_nw;
static lk_task* lk_q_head;
static lk_task* lk_q_tail;
static int64_t lk_qn;       // 全局队列的长度（原子地读：是 0 就不用拿锁）
static int lk_idle;         // 在条件变量上等着的工作线程数
// 已经叫醒、还没醒来的线程数（最多 1）。每放一个任务就叫醒一个线程的话，一大群线程醒来抢同一把锁，
// 多数抢到了又没有活干（lredis 的采样里这占了大半时间），所以同时只叫醒一个，它醒来以后看情况再叫下一个
static int lk_npend;
static bool lk_watching;    // 有一个空闲线程在看守：等网络事件、定时器到期、runnext 里等得太久的任务
static char* lk_pool[LK_STACK_POOL];
static int lk_npool;
static lk_task lk_main_task;

static __thread lk_worker* lk_w_;
// 不能内联，理由同 lk_slot_mt
static __attribute__((noinline)) lk_worker* lk_cur_w(void) { return lk_w_; }

static void lk_unlock_mu(void* m) {
  lk_tsan_take(m);
  pthread_mutex_unlock((pthread_mutex_t*)m);
}

// 挂起，切过去以后解开 mu（任务在这边拿着它）
static void lk_park(void (*after)(void*), void* arg);
static void lk_park_mu(pthread_mutex_t* mu) {
  lk_tsan_give(mu);
  lk_park(lk_unlock_mu, mu);
}

// 挂起时要解开两把锁：参数是放在任务栈上的两个指针（第二个可以是 NULL）。先取出来再解锁，
// 解开以后任务可能马上在别的线程上醒来、离开这一层函数
static void lk_unlock2(void* p) {
  pthread_mutex_t** m = (pthread_mutex_t**)p;
  pthread_mutex_t* a = m[0];
  pthread_mutex_t* b = m[1];
  if (b) pthread_mutex_unlock(b);
  pthread_mutex_unlock(a);
}

// 开始一次等待，返回它的编号。之后叫醒它的一方要用 lk_claim 抢这个编号
static int64_t lk_wait_begin(lk_task* t) {
  int64_t tok = ++t->gen;
  __atomic_store_n(&t->wait, tok, __ATOMIC_RELEASE);
  return tok;
}

static bool lk_claim(lk_task* t, int64_t tok) {
  int64_t e = tok;
  return __atomic_compare_exchange_n(&t->wait, &e, 0, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
}

// ---------- 事件循环：kqueue（macOS）/ epoll（Linux） ----------
// 任务读写 socket、accept 得到 EAGAIN 时挂起，等事件循环在这个 fd 可读 / 可写时叫醒它。
// 平时由看守线程在 lk_poll_wait 里等事件（顺便等最近的定时器），忙着的线程每调度 61 次不等待地查一次。
// 每个 fd 同时只会有一个任务在等（fd 属于一个 Conn / Listener，它只在一个任务手里），所以按 fd 下标记等待者就够了。
//
// fd 第一次要等某个方向时在事件循环里登记一次（边沿触发：kqueue 的 EV_CLEAR、epoll 的 EPOLLET），以后一直留着，
// 关闭时系统自动去掉。原来每次等待都登记一次“只触发一次”的事件，lhttp 里每个请求要多一次 kevent。
// 边沿触发只在状态变化时报一次，所以：
// - 等之前一定先试过读写（或 accept），得到 EAGAIN 才等；
// - 事件来的时候没人在等，就记下 LK_FD_READY，下一个等的人看到它就不挂起，回去重试读写。
//   醒来不保证真的就绪（可能是以前留下的记号），调用者重试还是 EAGAIN 就再等。
//
// fd 表不加锁：分成每页 1024 项，页分配以后不再移动，各项原子地读写。原来用一把锁的时候，lhttp 的 50 个连接
// 每次等数据都要抢它（采样里是第二大的开销）。
#define LK_FD_READY ((lk_task*)1)
#define LK_FD_NONBLOCK 4    // reg 里的一位：已经设了 O_NONBLOCK（只用于 Listener，见 lk_try_tcp_accept）
#define LK_FD_NOPOLL 8      // reg 里的一位：事件循环登记不了（比如 macOS 上的某些终端设备），只能阻塞着等（见 lk_fd_wait）
typedef struct {
  lk_task* w[2];            // 读、写各一个：NULL 没人等，LK_FD_READY 有过事件还没人用，其余是在等的任务（原子地读写）
  int64_t tok[2];           // 那次等待的编号：先写它，再写 w
  int64_t timeout_ms;       // set_timeout 设的读写超时，0 表示不超时（原子地读写）
  int reg;                  // 已经在事件循环里登记的方向（1 读，2 写）和 LK_FD_NONBLOCK。只有拥有 fd 的任务读写
} lk_fdst;

#define LK_FD_PAGE 1024
#define LK_FD_PAGES 1024    // fd 最大到 1024 * 1024
static lk_fdst* lk_fdpages[LK_FD_PAGES];
static int lk_pfd = -1;     // kqueue / epoll 的 fd
// 看守线程正在 lk_poll_wait 里等（这时要用 lk_poll_wake 叫醒它，条件变量叫不醒）。原子地读写
static bool lk_polling;
static bool lk_pwoken;      // 已经叫过看守线程、它还没醒（同样只叫一次）。原子地读写
static int64_t lk_wuntil;   // 看守线程这次最多等到什么时候（-1 写成 INT64_MAX）：更早的定时器要叫醒它。原子地读写

// fd 对应的那一项；页还没有时，create 为真就分配一页（几个线程同时分配时，CAS 输了的释放自己那页）
static lk_fdst* lk_fd_slot(int fd, bool create) {
  if (fd < 0 || fd >= LK_FD_PAGE * LK_FD_PAGES) return NULL;
  lk_fdst** pp = &lk_fdpages[fd / LK_FD_PAGE];
  lk_fdst* page = __atomic_load_n(pp, __ATOMIC_ACQUIRE);
  if (!page) {
    if (!create) return NULL;
    lk_fdst* fresh = (lk_fdst*)lk_alloc(sizeof(lk_fdst) * LK_FD_PAGE);
    lk_fdst* expected = NULL;
    if (__atomic_compare_exchange_n(pp, &expected, fresh, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
      page = fresh;
    } else {
      lk_free(fresh);
      page = expected;
    }
  }
  return &page[fd % LK_FD_PAGE];
}

#if defined(__APPLE__) || defined(__FreeBSD__)
#include <sys/event.h>
static void lk_poll_init(void) {
  lk_pfd = kqueue();
  if (lk_pfd < 0) lk_panic_c("无法创建 kqueue");
  fcntl(lk_pfd, F_SETFD, FD_CLOEXEC);
  struct kevent ev;
  EV_SET(&ev, 0, EVFILT_USER, EV_ADD | EV_CLEAR, 0, 0, NULL);
  kevent(lk_pfd, &ev, 1, NULL, 0, NULL);
}
static void lk_poll_wake(void) {
  struct kevent ev;
  EV_SET(&ev, 0, EVFILT_USER, 0, NOTE_TRIGGER, 0, NULL);
  kevent(lk_pfd, &ev, 1, NULL, 0, NULL);
}
// 登记 fd 的一个方向（边沿触发，一直留着）。mask 是登记以后所有已登记的方向（epoll 要一起给）
static bool lk_poll_reg(int fd, bool wr, int mask) {
  (void)mask;
  struct kevent ev;
  EV_SET(&ev, fd, wr ? EVFILT_WRITE : EVFILT_READ, EV_ADD | EV_CLEAR, 0, 0, NULL);
  return kevent(lk_pfd, &ev, 1, NULL, 0, NULL) == 0;
}
// 等事件，最多等到 until（单调时钟；-1 一直等，0 不等）。就绪的放进 out，每个是 fd * 2 + 方向（0 读，1 写），
// out 要能放 2 * LK_POLL_MAX 个；返回个数
#define LK_POLL_MAX 64
static int lk_poll_wait(int* out, int64_t until) {
  struct kevent evs[LK_POLL_MAX];
  struct timespec ts, *tp = NULL;
  if (until >= 0) {
    int64_t d = until == 0 ? 0 : until - lk_mono_ns();
    if (d < 0) d = 0;
    ts.tv_sec = (time_t)(d / 1000000000);
    ts.tv_nsec = (long)(d % 1000000000);
    tp = &ts;
  }
  int n = kevent(lk_pfd, NULL, 0, evs, LK_POLL_MAX, tp);
  int k = 0;
  for (int i = 0; i < n; i++) {
    if (evs[i].filter == EVFILT_READ) out[k++] = (int)evs[i].ident * 2;
    else if (evs[i].filter == EVFILT_WRITE) out[k++] = (int)evs[i].ident * 2 + 1;
  }
  return k;
}
#elif defined(__linux__)
#include <sys/epoll.h>
#include <sys/eventfd.h>
static int lk_efd = -1;     // 用来叫醒 epoll_wait 的 eventfd
static void lk_poll_init(void) {
  lk_pfd = epoll_create1(EPOLL_CLOEXEC);
  lk_efd = eventfd(0, EFD_NONBLOCK | EFD_CLOEXEC);
  if (lk_pfd < 0 || lk_efd < 0) lk_panic_c("无法创建 epoll");
  struct epoll_event ev = { .events = EPOLLIN, .data.fd = lk_efd };
  epoll_ctl(lk_pfd, EPOLL_CTL_ADD, lk_efd, &ev);
}
static void lk_poll_wake(void) {
  uint64_t one = 1;
  ssize_t r = write(lk_efd, &one, sizeof one);
  (void)r;
}
// epoll 一个 fd 只有一项：第一次 ADD，加方向时 MOD（关掉的 fd 会自动去掉，所以 reg 在关闭时清零）
static bool lk_poll_reg(int fd, bool wr, int mask) {
  struct epoll_event ev = { .events = EPOLLET | ((mask & 1) ? EPOLLIN | EPOLLRDHUP : 0) | ((mask & 2) ? EPOLLOUT : 0), .data.fd = fd };
  bool first = (mask & 3) == (wr ? 2 : 1);
  if (epoll_ctl(lk_pfd, first ? EPOLL_CTL_ADD : EPOLL_CTL_MOD, fd, &ev) == 0) return true;
  return epoll_ctl(lk_pfd, first ? EPOLL_CTL_MOD : EPOLL_CTL_ADD, fd, &ev) == 0;
}
#define LK_POLL_MAX 64
static int lk_poll_wait(int* out, int64_t until) {
  struct epoll_event evs[LK_POLL_MAX];
  int ms = -1;
  if (until == 0) ms = 0;
  else if (until > 0) {
    int64_t d = until - lk_mono_ns();
    ms = d <= 0 ? 0 : (int)((d + 999999) / 1000000);
  }
  int n = epoll_wait(lk_pfd, evs, LK_POLL_MAX, ms);
  int k = 0;
  for (int i = 0; i < n; i++) {
    if (evs[i].data.fd == lk_efd) {
      uint64_t x;
      ssize_t r = read(lk_efd, &x, sizeof x);
      (void)r;
      continue;
    }
    uint32_t e = evs[i].events;
    // 出错、对方关闭时两个方向都叫醒，读写会得到结果
    if (e & (EPOLLIN | EPOLLRDHUP | EPOLLHUP | EPOLLERR)) out[k++] = evs[i].data.fd * 2;
    if (e & (EPOLLOUT | EPOLLHUP | EPOLLERR)) out[k++] = evs[i].data.fd * 2 + 1;
  }
  return k;
}
#else
#error "Lark 的事件循环只支持 macOS（kqueue）和 Linux（epoll）"
#endif

// ---------- 运行队列 ----------
// 每个工作线程有自己的队列（自己的锁，平时只有自己用，偷的时候别的线程才来拿）。本线程上叫醒的、
// 事件循环和定时器叫醒的任务都放在本线程的队列里。全局队列只放 spawn 出来的任务，用调度器的锁。
// lredis 的采样里，所有线程抢调度器那一把锁占了大半时间，这样拆开以后只有睡下、醒来和 spawn 才用它。

// 有睡着的线程、又没有已经叫醒还没醒来的，就叫醒一个；都没有睡着、看守线程又在等事件，就叫醒看守线程（也只叫一次）。
// 不加锁先看一眼 lk_idle：看漏了不要紧，任务在某个线程的队列里，那个线程总会运行它，看守线程每 1 毫秒也会来偷
static void lk_wake_one(bool locked) {
  if (__atomic_load_n(&lk_idle, __ATOMIC_ACQUIRE) > 0) {
    if (!locked) pthread_mutex_lock(&lk_sched_mu);
    if (lk_idle > 0 && lk_npend == 0) {
      lk_npend = 1;
      pthread_cond_signal(&lk_sched_cv);
    }
    if (!locked) pthread_mutex_unlock(&lk_sched_mu);
  } else if (__atomic_load_n(&lk_polling, __ATOMIC_ACQUIRE) && !__atomic_exchange_n(&lk_pwoken, true, __ATOMIC_ACQ_REL)) {
    lk_poll_wake();
  }
}

// 放进全局队列（调度器的锁里）
static void lk_push_locked(lk_task* t) {
  t->next = NULL;
  if (lk_q_tail) lk_q_tail->next = t; else lk_q_head = t;
  lk_q_tail = t;
  __atomic_add_fetch(&lk_qn, 1, __ATOMIC_RELEASE);
  lk_wake_one(true);
}

static lk_task* lk_global_pop(void) {
  if (__atomic_load_n(&lk_qn, __ATOMIC_ACQUIRE) == 0) return NULL;
  pthread_mutex_lock(&lk_sched_mu);
  lk_task* t = lk_q_head;
  if (t) {
    lk_q_head = t->next;
    if (!lk_q_head) lk_q_tail = NULL;
    __atomic_sub_fetch(&lk_qn, 1, __ATOMIC_RELEASE);
  }
  pthread_mutex_unlock(&lk_sched_mu);
  return t;
}

// 一串任务（用 next 串着）放进 w 的队列尾
static void lk_local_push_list(lk_worker* w, lk_task* list) {
  if (!list) return;
  pthread_mutex_lock(&w->qmu);
  while (list) {
    lk_task* t = list;
    list = t->next;
    t->next = NULL;
    if (w->qt) w->qt->next = t; else w->qh = t;
    w->qt = t;
    __atomic_add_fetch(&w->qn, 1, __ATOMIC_RELEASE);
  }
  pthread_mutex_unlock(&w->qmu);
}

static lk_task* lk_local_pop(lk_worker* w) {
  if (__atomic_load_n(&w->qn, __ATOMIC_ACQUIRE) == 0) return NULL;
  pthread_mutex_lock(&w->qmu);
  lk_task* t = w->qh;
  if (t) {
    w->qh = t->next;
    if (!w->qh) w->qt = NULL;
    __atomic_sub_fetch(&w->qn, 1, __ATOMIC_RELEASE);
  }
  pthread_mutex_unlock(&w->qmu);
  return t;
}

// 从别的线程的队列里偷一半（至少一个）：第一个拿来运行，其余放进自己的队列
static lk_task* lk_steal(lk_worker* self) {
  int start = (int)(self->tick % (uint64_t)lk_nw);
  for (int k = 0; k < lk_nw; k++) {
    lk_worker* o = &lk_ws[(start + k) % lk_nw];
    if (o == self || __atomic_load_n(&o->qn, __ATOMIC_ACQUIRE) == 0) continue;
    pthread_mutex_lock(&o->qmu);
    int64_t take = (o->qn + 1) / 2;
    lk_task* first = NULL;
    lk_task* rest = NULL;
    lk_task* rest_tail = NULL;
    for (int64_t i = 0; i < take && o->qh; i++) {
      lk_task* t = o->qh;
      o->qh = t->next;
      if (!o->qh) o->qt = NULL;
      __atomic_sub_fetch(&o->qn, 1, __ATOMIC_RELEASE);
      t->next = NULL;
      if (!first) first = t;
      else {
        if (rest_tail) rest_tail->next = t; else rest = t;
        rest_tail = t;
      }
    }
    pthread_mutex_unlock(&o->qmu);
    if (rest) lk_local_push_list(self, rest);
    if (first) return first;
  }
  return NULL;
}

// 让 t 可以运行。在任务里叫醒别的任务时放进本线程的“下一个”位置，原来在那里的挪到本线程的队列，
// 再看要不要叫醒一个空闲线程来偷。不在任务里（调度循环里）时放进全局队列。locked：调用者拿着调度器的锁
static void lk_ready_(lk_task* t, bool locked) {
  lk_worker* w = lk_cur_w();
  if (w && w->cur) {
    lk_task* old = __atomic_exchange_n(&w->runnext, t, __ATOMIC_ACQ_REL);
    if (!old) return;
    old->next = NULL;
    lk_local_push_list(w, old);
    lk_wake_one(locked);
    return;
  }
  if (!locked) pthread_mutex_lock(&lk_sched_mu);
  lk_push_locked(t);
  if (!locked) pthread_mutex_unlock(&lk_sched_mu);
}
static void lk_ready(lk_task* t) { lk_ready_(t, false); }

// 就绪的 fd（lk_poll_wait 给的 fd * 2 + 方向）：有任务在等就拿走它、抢它的等待编号，抢到的串成一串返回；
// 没人等就记下 LK_FD_READY。叫醒了任务以后不留记号：它醒来就会去读写，不然下一次等待会白白多试一次
static lk_task* lk_poll_collect(const int* evs, int n) {
  lk_task* woke = NULL;
  for (int i = 0; i < n; i++) {
    lk_fdst* s = lk_fd_slot(evs[i] / 2, false);
    if (!s) continue;
    lk_task** wp = &s->w[evs[i] % 2];
    lk_task* cur = __atomic_load_n(wp, __ATOMIC_ACQUIRE);
    while (cur != LK_FD_READY && !__atomic_compare_exchange_n(wp, &cur, cur ? NULL : LK_FD_READY, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {}
    if (!cur || cur == LK_FD_READY) continue;
    int64_t tok = __atomic_load_n(&s->tok[evs[i] % 2], __ATOMIC_ACQUIRE);
    if (lk_claim(cur, tok)) {
      cur->fired = 0;
      cur->next = woke;
      woke = cur;
    }
  }
  return woke;
}

// ---------- 定时器堆（每个工作线程一个，各用各的锁） ----------
// 每个任务最多在一个堆里有一项：再次等待时原地改到期时间。被通道、事件叫醒的任务，它的定时器留在堆里不管，
// 到期时抢不到编号就作废；所以堆的大小不超过任务数，不会像每次 select 都加一个那样越积越多。
// 新的一项放进当前线程的堆；任务换了线程以后，它的那一项还留在原来的堆里，在那里原地改。
// 原来全进程只有一个堆、一把锁，lhttp 每次读都要设空闲超时，换成边沿触发以后这把锁成了最大的等锁。
// first 是最早的到期时间（没有是 INT64_MAX），原子地读：还没到期时不用拿锁

// 锁上任务 t 的那一项所在的堆（还没有就是当前线程的堆）。t->theap 只会被别人改成 NULL（到期、结束时拿掉），
// 改成别的值的只有 t 自己的等待，所以锁上以后再看一次没变就行
static lk_theap* lk_timer_lock(lk_task* t) {
  for (;;) {
    lk_theap* h = __atomic_load_n(&t->theap, __ATOMIC_ACQUIRE);
    lk_theap* l = h ? h : &lk_cur_w()->tm;
    pthread_mutex_lock(&l->mu);
    if (__atomic_load_n(&t->theap, __ATOMIC_ACQUIRE) == h) return l;
    pthread_mutex_unlock(&l->mu);
  }
}

static void lk_heap_put(lk_theap* h, int64_t i, lk_task* t) {
  h->th[i] = t;
  t->hidx = i + 1;
}

static void lk_heap_up(lk_theap* h, int64_t i) {
  lk_task* t = h->th[i];
  while (i > 0 && h->th[(i - 1) / 2]->tat > t->tat) {
    lk_heap_put(h, i, h->th[(i - 1) / 2]);
    i = (i - 1) / 2;
  }
  lk_heap_put(h, i, t);
}

static void lk_heap_down(lk_theap* h, int64_t i) {
  lk_task* t = h->th[i];
  for (;;) {
    int64_t c = 2 * i + 1;
    if (c >= h->n) break;
    if (c + 1 < h->n && h->th[c + 1]->tat < h->th[c]->tat) c++;
    if (h->th[c]->tat >= t->tat) break;
    lk_heap_put(h, i, h->th[c]);
    i = c;
  }
  lk_heap_put(h, i, t);
}

static void lk_tfirst_update(lk_theap* h) {
  __atomic_store_n(&h->first, h->n > 0 ? h->th[0]->tat : INT64_MAX, __ATOMIC_RELEASE);
}

// h 是 lk_timer_lock(t) 锁上的堆
static void lk_timer_del_locked(lk_theap* h, lk_task* t) {
  if (!t->hidx) return;
  int64_t i = t->hidx - 1;
  t->hidx = 0;
  __atomic_store_n(&t->theap, NULL, __ATOMIC_RELEASE);
  lk_task* last = h->th[--h->n];
  if (i != h->n) {
    lk_heap_put(h, i, last);
    lk_heap_up(h, i);
    lk_heap_down(h, last->hidx - 1);
  }
  lk_tfirst_update(h);
}

// 任务 t 的这次等待（编号 tok）最多等到 at。h 是 lk_timer_lock(t) 锁上的堆
static void lk_timer_set_locked(lk_theap* h, lk_task* t, int64_t at, int64_t tok) {
  t->ttok = tok;
  t->tat = at;
  if (t->hidx) {
    int64_t i = t->hidx - 1;
    lk_heap_up(h, i);
    lk_heap_down(h, t->hidx - 1);
  } else {
    if (h->n == h->cap) {
      h->cap = h->cap * 2 + 16;
      h->th = (lk_task**)lk_realloc(h->th, sizeof(lk_task*) * (size_t)h->cap);
    }
    h->th[h->n] = t;
    t->hidx = ++h->n;
    __atomic_store_n(&t->theap, h, __ATOMIC_RELEASE);
    lk_heap_up(h, h->n - 1);
  }
  lk_tfirst_update(h);
  // 比看守线程要等到的时间还早：叫醒它，让它按新的时间等
  if (at < __atomic_load_n(&lk_wuntil, __ATOMIC_ACQUIRE) && __atomic_load_n(&lk_polling, __ATOMIC_ACQUIRE) &&
      !__atomic_exchange_n(&lk_pwoken, true, __ATOMIC_ACQ_REL)) {
    lk_poll_wake();
  }
}

// 一个堆里到期的定时器：抢到等待编号的接到 woke 前面。还没有到期的就不拿锁
static lk_task* lk_timers_collect1(lk_theap* h, int64_t now, lk_task* woke) {
  if (__atomic_load_n(&h->first, __ATOMIC_ACQUIRE) > now) return woke;
  pthread_mutex_lock(&h->mu);
  while (h->n > 0 && h->th[0]->tat <= now) {
    lk_task* t = h->th[0];
    lk_timer_del_locked(h, t);
    if (lk_claim(t, t->ttok)) {
      t->fired = -1;
      t->next = woke;
      woke = t;
    }
  }
  pthread_mutex_unlock(&h->mu);
  return woke;
}

// all 为假时只看本线程的堆
static lk_task* lk_timers_collect(lk_worker* w, bool all) {
  int64_t now = lk_mono_ns();
  if (!all) return lk_timers_collect1(&w->tm, now, NULL);
  lk_task* woke = NULL;
  for (int i = 0; i < lk_nw; i++) woke = lk_timers_collect1(&lk_ws[i].tm, now, woke);
  return woke;
}

// 所有堆里最早的到期时间（没有是 INT64_MAX）
static int64_t lk_timers_first(void) {
  int64_t m = INT64_MAX;
  for (int i = 0; i < lk_nw; i++) {
    int64_t f = __atomic_load_n(&lk_ws[i].tm.first, __ATOMIC_ACQUIRE);
    if (f < m) m = f;
  }
  return m;
}

// 看守线程每隔一会儿看一次各线程的 runnext：连着两次看到同一个任务，说明那个线程一直在算、没有让出，把它拿过来运行
static lk_task* lk_steal_stale_locked(lk_worker* self) {
  for (int i = 0; i < lk_nw; i++) {
    lk_worker* o = &lk_ws[i];
    if (o == self) continue;
    lk_task* rn = __atomic_load_n(&o->runnext, __ATOMIC_ACQUIRE);
    if (rn && rn == o->rn_seen) {
      o->rn_seen = NULL;
      lk_task* t = __atomic_exchange_n(&o->runnext, NULL, __ATOMIC_ACQ_REL);
      if (t) return t;
    } else {
      o->rn_seen = rn;
    }
  }
  return NULL;
}

#define LK_WATCH_NS 1000000     // 看守线程至少每 1 毫秒醒一次（有任务活着时）

// 取下一个要运行的任务，没有就等。依次看：本线程的 runnext、本线程的队列、全局队列、偷别的线程的队列。
// 每 61 次先看全局队列（免得它被饿着），顺便不等待地查一次网络事件（一直有任务可运行时，看守线程不会去等事件）。
// 定时器平时只看本线程的堆，每 61 次和看守时看所有线程的（别的线程可能正睡着）。
// 都没有时，一个空闲线程当看守：在 lk_poll_wait 里等网络事件，超时是最近的定时器（有任务活着时最多 1 毫秒）；其余的睡在条件变量上
static lk_task* lk_next(lk_worker* w) {
  lk_task* t = NULL;
  bool check = ++w->tick % 61 == 0;
  if (!check) {
    t = __atomic_exchange_n(&w->runnext, NULL, __ATOMIC_ACQ_REL);
    if (t) return t;
  }
  int ready[2 * LK_POLL_MAX];
  lk_task* woke = lk_timers_collect(w, check);
  if (check && !__atomic_load_n(&lk_polling, __ATOMIC_ACQUIRE)) {
    lk_task* more = lk_poll_collect(ready, lk_poll_wait(ready, 0));
    while (more) {
      lk_task* x = more;
      more = x->next;
      x->next = woke;
      woke = x;
    }
  }
  if (woke) {
    bool many = woke->next != NULL;
    lk_local_push_list(w, woke);
    if (many) lk_wake_one(false);
  }
  if (check && (t = lk_global_pop())) return t;
  for (;;) {
    if ((t = lk_local_pop(w))) return t;
    if ((t = __atomic_exchange_n(&w->runnext, NULL, __ATOMIC_ACQ_REL))) return t;
    if ((t = lk_global_pop())) return t;
    if ((t = lk_steal(w))) return t;
    pthread_mutex_lock(&lk_sched_mu);
    if (lk_q_head) {
      pthread_mutex_unlock(&lk_sched_mu);
      continue;
    }
    if (!lk_watching) {
      lk_watching = true;
      int64_t until = lk_timers_first();
      if (until == INT64_MAX) until = -1;
      if (__atomic_load_n(&lk_nthreads, __ATOMIC_RELAXED) > 0) {
        int64_t tick = lk_mono_ns() + LK_WATCH_NS;
        if (until < 0 || tick < until) until = tick;
      }
      __atomic_store_n(&lk_wuntil, until < 0 ? INT64_MAX : until, __ATOMIC_RELEASE);
      __atomic_store_n(&lk_pwoken, false, __ATOMIC_RELEASE);
      __atomic_store_n(&lk_polling, true, __ATOMIC_RELEASE);
      pthread_mutex_unlock(&lk_sched_mu);
      int n = lk_poll_wait(ready, until);
      __atomic_store_n(&lk_polling, false, __ATOMIC_RELEASE);
      woke = lk_poll_collect(ready, n);
      lk_task* timed = lk_timers_collect(w, true);
      while (timed) {
        lk_task* x = timed;
        timed = x->next;
        x->next = woke;
        woke = x;
      }
      pthread_mutex_lock(&lk_sched_mu);
      lk_watching = false;
      if (!woke && until >= 0 && lk_mono_ns() >= until) t = lk_steal_stale_locked(w);
      // 看守的位置空出来了：叫醒一个睡着的线程来接
      if (lk_idle > 0 && lk_npend == 0) {
        lk_npend = 1;
        pthread_cond_signal(&lk_sched_cv);
      }
      pthread_mutex_unlock(&lk_sched_mu);
      if (woke) {
        bool many = woke->next != NULL;
        lk_local_push_list(w, woke);
        if (many) lk_wake_one(false);
      }
      if (t) return t;
    } else {
      __atomic_add_fetch(&lk_idle, 1, __ATOMIC_ACQ_REL);
      pthread_cond_wait(&lk_sched_cv, &lk_sched_mu);
      __atomic_sub_fetch(&lk_idle, 1, __ATOMIC_ACQ_REL);
      lk_npend = 0;
      pthread_mutex_unlock(&lk_sched_mu);
    }
  }
}

// 挂起当前任务，切回本线程的调度循环；切过去以后调度循环调用 after(arg)。
// 叫醒它的一方要先拿到 after 解开的那把锁，所以那时任务的栈指针一定已经存好了
static void lk_park(void (*after)(void*), void* arg) {
  lk_worker* w = lk_cur_w();
  lk_task* t = w->cur;
  w->after = after;
  w->after_arg = arg;
  lk_fib_switch(w->fib);
  lk_swap_ctx(&t->sp, w->sp);
}

// 先做上一个任务挂起或结束时留下的事（解锁、释放），再取下一个任务。
// 必须放在每轮的开头：0 号线程的循环是主任务第一次挂起时才开始的，那时也有一个锁等着解开
static void lk_worker_loop(void* p) {
  lk_worker* w = (lk_worker*)p;
  lk_w_ = w;
  for (;;) {
    w->cur = NULL;
    if (w->after) {
      void (*f)(void*) = w->after;
      w->after = NULL;
      f(w->after_arg);
    }
    if (w->dead) {
      lk_task* d = w->dead;
      w->dead = NULL;
      if (d->stack) munmap(d->stack, LK_STACK);
      lk_fib_free(d->fib);
      lk_free(d);
    }
    lk_task* t = lk_next(w);
    w->cur = t;
#ifndef LK_NOTRACE
    lk_slot_ = (lk_frame**)t->topp;
#endif
    lk_fib_switch(t->fib);
    lk_swap_ctx(&w->sp, t->sp);
  }
}

// ---------- 栈溢出 ----------
// 递归太深时栈指针碰到保护页，进程收到 SIGSEGV（macOS 上有时是 SIGBUS）。系统默认的处理是不留任何提示地退出，
// 这里改成和 panic 一样：打印“栈溢出”和调用栈，退出码 101。
// 原来的栈已经满了，所以处理函数在另外一块栈上运行（sigaltstack，每个线程一块）。
// 出错的地址不在栈的保护页附近时是别的内存错误（Lark 代码本不该有，多半来自 extern "c" 的 C 代码），也报出来。
// 处理函数里打印只用 write，最后 _exit(101)：出错时可能正拿着 malloc 的锁，printf、exit 都可能卡住。
// 只有 fflush(stdout) 例外：先把已经 print 的内容写出去，stdio 的锁是可重入的，同一个线程再拿不会卡住。
// 加了 AddressSanitizer 时不装：它自己会报栈溢出，而且报得更细。
#define LK_ALTSTACK ((size_t)64 << 10)

#if defined(__has_feature)
#if __has_feature(address_sanitizer)
#define LK_ASAN 1
#endif
#endif
#ifdef __SANITIZE_ADDRESS__
#define LK_ASAN 1
#endif

static char* lk_main_stack_hi;     // 主线程栈的顶（lk_init 里一个局部变量的地址）
static size_t lk_main_stack_lim;   // 主线程栈最大多大（RLIMIT_STACK）；不限时为 0
static size_t lk_page;

static void __attribute__((unused)) lk_sig_puts(const char* s) {
  ssize_t r = write(2, s, strlen(s));
  (void)r;
}

static void __attribute__((unused)) lk_sig_putn(int64_t n) {
  char buf[24];
  int i = 23;
  buf[i] = 0;
  if (n == 0) buf[--i] = '0';
  for (; n > 0 && i > 0; n /= 10) buf[--i] = (char)('0' + n % 10);
  lk_sig_puts(buf + i);
}

// 和 lk_trace 一样从里到外打印，但连着的同一处调用（递归）合成一行：栈溢出时往往有几万层
static void __attribute__((unused)) lk_sig_trace(void) {
#ifndef LK_NOTRACE
  lk_frame* f = *lk_slot();
  int shown = 0;
  for (; f && shown < 20; shown++) {
    int64_t same = 0;
    lk_frame* g = f->prev;
    for (; g && g->line == f->line && strcmp(g->fn, f->fn) == 0 && strcmp(g->file, f->file) == 0; g = g->prev) same++;
    lk_sig_puts("  在 ");
    lk_sig_puts(f->fn);
    lk_sig_puts("（");
    lk_sig_puts(f->file);
    lk_sig_puts(":");
    lk_sig_putn(f->line);
    lk_sig_puts("）\n");
    if (same > 0) {
      lk_sig_puts("  …（同一处又重复了 ");
      lk_sig_putn(same);
      lk_sig_puts(" 层）\n");
    }
    f = g;
  }
  if (f) {
    int64_t rest = 0;
    for (; f; f = f->prev) rest++;
    lk_sig_puts("  …（还有 ");
    lk_sig_putn(rest);
    lk_sig_puts(" 层）\n");
  }
#endif
}

// 出错的地址是不是撞到了栈底：任务的栈看它的保护页，主线程的栈看 RLIMIT_STACK 的边界。
// 一层的局部变量很大时可能一下跳过保护页，所以往下多算 1 MB
static bool __attribute__((unused)) lk_hit_stack(char* a) {
  char* lo = NULL;
  char* hi = NULL;
  lk_worker* w = lk_started ? lk_w_ : NULL;
  if (w && w->cur && w->cur->stack) {
    lo = w->cur->stack;
    hi = lo + lk_page;
  } else if (lk_main_stack_lim > 0 && (w == NULL || w->cur == &lk_main_task)) {
    hi = lk_main_stack_hi - lk_main_stack_lim + ((size_t)1 << 20);
    lo = lk_main_stack_hi - lk_main_stack_lim;
  } else {
    return false;
  }
  return a >= lo - ((size_t)1 << 20) && a < hi;
}

static void __attribute__((unused)) lk_on_fault(int sig, siginfo_t* si, void* uc) {
  (void)uc;
  fflush(stdout);
  if (lk_hit_stack((char*)si->si_addr)) {
    lk_sig_puts("panic: 栈溢出（递归太深，或者一层里的局部变量太大）\n");
  } else {
    lk_sig_puts(sig == SIGBUS ? "panic: 内存错误（SIGBUS）" : "panic: 内存错误（SIGSEGV）");
    lk_sig_puts("：访问了无效的地址，多半来自 extern \"c\" 调用的 C 代码\n");
  }
  lk_sig_trace();
  if (lk_term_is_raw || lk_term_alt_on) (void)lark_term_restore();
  _exit(101);
}

// 给当前线程准备一块处理信号用的栈
static void lk_guard_thread(void) {
#ifndef LK_ASAN
  stack_t ss;
  memset(&ss, 0, sizeof ss);
  ss.ss_sp = mmap(NULL, LK_ALTSTACK, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANON, -1, 0);
  if (ss.ss_sp == MAP_FAILED) return;
  ss.ss_size = LK_ALTSTACK;
  sigaltstack(&ss, NULL);
#endif
}

static void lk_guard_install(char* stack_hi) {
#ifndef LK_ASAN
  lk_page = (size_t)sysconf(_SC_PAGESIZE);
  lk_main_stack_hi = stack_hi;
  struct rlimit rl;
  if (getrlimit(RLIMIT_STACK, &rl) == 0 && rl.rlim_cur != RLIM_INFINITY) lk_main_stack_lim = (size_t)rl.rlim_cur;
  lk_guard_thread();
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_sigaction = lk_on_fault;
  sa.sa_flags = SA_SIGINFO | SA_ONSTACK | SA_RESETHAND;   // 处理函数自己出错时按默认处理退出，不会死循环
  sigemptyset(&sa.sa_mask);
  sigaction(SIGSEGV, &sa, NULL);
  sigaction(SIGBUS, &sa, NULL);
#else
  (void)stack_hi;
#endif
}

static void* lk_worker_thread(void* p) {
  ((lk_worker*)p)->fib = lk_fib_current();
  lk_guard_thread();
  lk_worker_loop(p);
  return NULL;
}

// 第一次 spawn（或者第一次要等待）时启动：当前线程成为 0 号工作线程，正在运行的代码成为主任务。
// 0 号线程的调度循环要另外一块栈（进程原来的栈归主任务）
static void lk_sched_start(void) {
  lk_started = true;
  const char* e = getenv("LARK_PROCS");
  int n = e ? atoi(e) : (int)sysconf(_SC_NPROCESSORS_ONLN);
  if (n < 1) n = 1;
  if (n > 256) n = 256;
  lk_nw = n;
  lk_ws = (lk_worker*)lk_alloc(sizeof(lk_worker) * (size_t)n);
  for (int i = 0; i < n; i++) {
    pthread_mutex_init(&lk_ws[i].qmu, NULL);
    pthread_mutex_init(&lk_ws[i].tm.mu, NULL);
    lk_ws[i].tm.first = INT64_MAX;
  }
#ifndef LK_NOTRACE
  lk_main_task.topp = (void**)&lk_main_top;
  lk_slot_ = &lk_main_top;   // 主任务的帧一直挂在 lk_main_top 上
#endif
  lk_worker* w0 = &lk_ws[0];
  w0->cur = &lk_main_task;
  lk_w_ = w0;
  char* st = lk_stack_new(LK_STACK);
  w0->sp = lk_ctx_init(st + LK_STACK, lk_worker_loop, w0);
  w0->fib = lk_fib_new();
  lk_main_task.fib = lk_fib_current();
  lk_poll_init();
  for (int i = 1; i < n; i++) {
    if (pthread_create(&lk_ws[i].th, NULL, lk_worker_thread, &lk_ws[i]) != 0) lk_panic_c("无法创建工作线程");
  }
}

// 当前任务（没启动调度器时先启动，当前代码就成了主任务）
static lk_task* lk_self(void) {
  if (!lk_started) lk_sched_start();
  return lk_cur_w()->cur;
}

// lk_fd_wait 挂起以后由调度循环做的事：设定时器（有超时时），再登记等待者。
// 一定要等任务切走以后才登记：登记以后事件随时可能叫醒它，那时它的栈指针必须已经存好了。
// 参数在挂起的任务的栈上，先全部取出来：登记完它就可能在别的线程上醒来、离开 lk_fd_wait。
// 有超时时，定时器堆的锁包住设定时器和登记等待者（不跨过切换）：这样定时器到期叫醒它时，登记一定已经写完了，
// lk_fd_wait 撤掉的就是这一次的登记。解锁以后不再碰任务。
// 登记时发现 LK_FD_READY（挂起前后来了事件）：不等了，自己抢编号、放回本线程的队列
typedef struct { lk_fdst* s; lk_task* t; int64_t tok; int64_t deadline; bool wr; } lk_fdw_arg;

static void lk_fd_wait_after(void* p) {
  lk_fdw_arg a = *(lk_fdw_arg*)p;
  bool timed = a.deadline >= 0;
  lk_theap* h = NULL;
  if (timed) {
    h = lk_timer_lock(a.t);
    lk_timer_set_locked(h, a.t, a.deadline, a.tok);
  }
  lk_task** wp = &a.s->w[a.wr];
  __atomic_store_n(&a.s->tok[a.wr], a.tok, __ATOMIC_RELEASE);
  lk_task* e = NULL;
  bool again = false;
  if (!__atomic_compare_exchange_n(wp, &e, a.t, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) {
    // e 只能是 LK_FD_READY：这个方向只有这个任务会等
    __atomic_store_n(wp, NULL, __ATOMIC_RELEASE);
    again = lk_claim(a.t, a.tok);
  }
  if (h) pthread_mutex_unlock(&h->mu);
  if (again) {
    a.t->fired = 0;
    a.t->next = NULL;
    lk_local_push_list(lk_cur_w(), a.t);
  }
}

// 登记不了事件循环的 fd：用 poll 阻塞着等（占着工作线程，但不会永远等不到）。返回 false 表示到时间了
static bool lk_fd_block_wait(int fd, bool wr, int64_t deadline) {
  struct pollfd p = { fd, (short)(wr ? POLLOUT : POLLIN), 0 };
  for (;;) {
    int ms = -1;
    if (deadline >= 0) {
      int64_t d = deadline - lk_mono_ns();
      if (d <= 0) return false;
      ms = (int)((d + 999999) / 1000000);
    }
    int r = poll(&p, 1, ms);
    if (r < 0 && errno == EINTR) continue;
    return r != 0;
  }
}

// 当前任务等 fd 可读（wr 为假）或可写，最多等到 deadline（单调时钟，-1 不限）。返回 false 表示到时间了。
// 调用者刚得到 EAGAIN。醒来不保证真的就绪（可能是以前留下的记号），调用者要重试读写，还是 EAGAIN 就再等
static bool lk_fd_wait(int fd, bool wr, int64_t deadline) {
  lk_task* t = lk_cur_w()->cur;
  if (deadline >= 0 && lk_mono_ns() >= deadline) return false;
  lk_fdst* s = lk_fd_slot(fd, true);
  if (!s) lk_panic_c("fd 太大，事件循环登记不了");
  int bit = wr ? 2 : 1;
  if (!(s->reg & bit)) {
    s->reg |= bit;
    if (!lk_poll_reg(fd, wr, s->reg & 3)) s->reg = (s->reg & ~bit) | LK_FD_NOPOLL;
  }
  if (s->reg & LK_FD_NOPOLL) return lk_fd_block_wait(fd, wr, deadline);
  // 已经有过事件：不挂起，回去重试
  lk_task* r = LK_FD_READY;
  if (__atomic_compare_exchange_n(&s->w[wr], &r, NULL, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE)) return true;
  int64_t tok = lk_wait_begin(t);
  t->fired = 0;
  lk_fdw_arg a = { s, t, tok, deadline, wr };
  lk_park(lk_fd_wait_after, &a);
  if (t->fired != -1) return true;
  // 到时间了：撤掉登记（事件循环可能刚好拿走了，那就什么都不用做）
  lk_task* expected = t;
  __atomic_compare_exchange_n(&s->w[wr], &expected, NULL, false, __ATOMIC_ACQ_REL, __ATOMIC_ACQUIRE);
  return false;
}

// 这个 fd 的读写超时对应的截止时间（-1 表示不超时）
static int64_t lk_fd_deadline(int fd) {
  lk_fdst* s = lk_fd_slot(fd, false);
  int64_t ms = s ? __atomic_load_n(&s->timeout_ms, __ATOMIC_RELAXED) : 0;
  return ms > 0 ? lk_mono_ns() + ms * 1000000 : -1;
}

static void lk_fd_set_timeout(int fd, int64_t ms) {
  lk_fdst* s = lk_fd_slot(fd, true);
  if (s) __atomic_store_n(&s->timeout_ms, ms, __ATOMIC_RELAXED);
}

// 调度器启动以后的 Listener 不阻塞（只设一次）
static void lk_fd_nonblock(int fd) {
  lk_fdst* s = lk_fd_slot(fd, true);
  if (s && (s->reg & LK_FD_NONBLOCK)) return;
  int fl = fcntl(fd, F_GETFL);
  if (fl >= 0) fcntl(fd, F_SETFL, fl | O_NONBLOCK);
  if (s) s->reg |= LK_FD_NONBLOCK;
}

// 关闭 fd 之前调用：忘掉它的超时、登记和记号（系统在关闭时去掉事件循环里的登记，fd 的号码会被重用）
static void lk_fd_forget(int fd) {
  lk_fdst* s = lk_fd_slot(fd, false);
  if (!s) return;
  __atomic_store_n(&s->timeout_ms, 0, __ATOMIC_RELAXED);
  s->reg = 0;
  __atomic_store_n(&s->w[0], NULL, __ATOMIC_RELEASE);
  __atomic_store_n(&s->w[1], NULL, __ATOMIC_RELEASE);
}

// 任务的入口（经 lk_task_boot 进来）。结束时先把它从定时器堆里拿掉（可能还留着作废的定时器），
// 再在调度器的锁里：scope 的计数减一（最后一个叫醒块尾等着的任务）、栈放回池里，
// 然后切回调度循环，由它解锁、释放任务本身。切走之前不能解锁：池里的栈还在用着
static void lk_task_main(void* p) {
  lk_task* t = (lk_task*)p;
  t->fn(t->arg);
  if (__atomic_load_n(&t->theap, __ATOMIC_ACQUIRE)) {
    lk_theap* h = lk_timer_lock(t);
    lk_timer_del_locked(h, t);
    pthread_mutex_unlock(&h->mu);
  }
  pthread_mutex_lock(&lk_sched_mu);
  __atomic_fetch_sub(&lk_nthreads, 1, __ATOMIC_RELAXED);
  lk_scope* s = t->scope;
  if (--s->live == 0 && s->waiter) {
    lk_task* wt = s->waiter;
    s->waiter = NULL;
    lk_ready_(wt, true);
  }
  if (lk_npool < LK_STACK_POOL) {
    lk_pool[lk_npool++] = t->stack;
    t->stack = NULL;
  }
  lk_worker* w = lk_cur_w();
  w->dead = t;
  w->after = lk_unlock_mu;
  w->after_arg = &lk_sched_mu;
  lk_tsan_give(&lk_sched_mu);
  lk_fib_switch(w->fib);
  lk_swap_ctx(&t->sp, w->sp);
}

// spawn(f, arg)：准备好任务放进全局队列，spawn 的一方接着运行。
// lk_nthreads 在任务能运行之前加一，所以从这时起引用计数都用原子操作（见 lk_rc_inc）
static void __attribute__((unused)) lk_spawn(lk_scope* s, void* (*f)(void*), void* arg) {
  __atomic_fetch_add(&lk_nthreads, 1, __ATOMIC_RELAXED);
  if (!lk_started) lk_sched_start();
  lk_task* t = (lk_task*)lk_alloc(sizeof(lk_task));
  t->fn = f;
  t->arg = arg;
  t->scope = s;
  t->topp = &t->top;
  pthread_mutex_lock(&lk_sched_mu);
  t->stack = lk_npool > 0 ? lk_pool[--lk_npool] : lk_stack_new(LK_STACK);
  t->sp = lk_ctx_init(t->stack + LK_STACK, lk_task_main, t);
  t->fib = lk_fib_new();
  s->live++;
  lk_push_locked(t);
  pthread_mutex_unlock(&lk_sched_mu);
}

// scope 块尾：等块里 spawn 的任务都结束
static void __attribute__((unused)) lk_scope_end(lk_scope* s) {
  if (!lk_started) return;
  pthread_mutex_lock(&lk_sched_mu);
  if (s->live == 0) {
    pthread_mutex_unlock(&lk_sched_mu);
    return;
  }
  s->waiter = lk_cur_w()->cur;
  lk_park_mu(&lk_sched_mu);
}

static void __attribute__((unused)) lk_sleep_ms(int64_t ms) {
  if (ms <= 0) return;
  if (!lk_started) {
    struct timespec ts = { (time_t)(ms / 1000), (long)((ms % 1000) * 1000000) };
    nanosleep(&ts, NULL);
    return;
  }
  lk_task* t = lk_cur_w()->cur;
  lk_theap* h = lk_timer_lock(t);
  int64_t tok = lk_wait_begin(t);
  lk_timer_set_locked(h, t, lk_mono_ns() + ms * 1000000, tok);
  lk_park_mu(&h->mu);
}

// ---------- Mutex[T] ----------
// lock m as x { … } 用的锁。锁着的任务可能在块里等待（recv、读网络），醒来时在别的系统线程上，
// 所以不能直接用 pthread 的锁（必须由加锁的线程解锁）：owner 记下持有它的任务，没抢到的任务挂在链表上挂起。
// - 加锁：owner 从 NULL 用 CAS 改成自己。抢不到先空转一会儿（锁里的代码一般很短），还不行再排队挂起。
// - 解锁：owner 改回 NULL；有人排队才拿 mu，叫醒最前面的那个，让它回去重新抢。
// 解锁时不直接把锁交给排队的任务：那样一旦有过一次冲突，之后每次加锁都要挂起、等调度器叫醒（锁交给了一个还没运行的任务，
// 别人只能接着排队），lhttp 的共享缓存这样做吞吐掉了四成。现在正在运行的任务可以直接抢到，醒来的任务没抢到就排回队首。
// nwait 是在排队（或正要排队）的任务数：先加一再最后试一次 CAS，解锁的一方先放开 owner 再看 nwait（都是 seq_cst），
// 所以要么等的人抢到了，要么解锁的人看到有人在等，不会两边都错过。mu 只保护链表，不会跨过挂起。
// 调度器没启动时（程序没有用并发）当前任务算作主任务。同一个任务再锁一次会永远等下去，直接报错退出
typedef struct lk_mwaiter {
  lk_task* t;
  int64_t tok;
  struct lk_mwaiter* next;
} lk_mwaiter;

typedef struct lk_mutex {
  lk_task* owner;           // 持有锁的任务，NULL 表示没锁（原子地读写）
  int64_t nwait;            // 原子地读写
  pthread_mutex_t mu;       // 保护 head、tail
  lk_mwaiter* head;
  lk_mwaiter* tail;
} lk_mutex;

#if defined(__aarch64__)
#define lk_cpu_relax() __asm__ __volatile__("yield")
#else
#define lk_cpu_relax() __asm__ __volatile__("pause")
#endif
#define LK_MUTEX_SPIN 100

static void __attribute__((unused)) lk_mutex_init(lk_mutex* m) {
  pthread_mutex_init(&m->mu, NULL);
  m->owner = NULL;
  m->nwait = 0;
  m->head = m->tail = NULL;
}

static void __attribute__((unused)) lk_mutex_destroy(lk_mutex* m) { pthread_mutex_destroy(&m->mu); }

static bool lk_mutex_try(lk_mutex* m, lk_task* t) {
  lk_task* e = NULL;
  return __atomic_compare_exchange_n(&m->owner, &e, t, false, __ATOMIC_SEQ_CST, __ATOMIC_RELAXED);
}

static void __attribute__((unused)) lk_mutex_lock(lk_mutex* m) {
  lk_task* t = lk_started ? lk_cur_w()->cur : &lk_main_task;
  if (lk_mutex_try(m, t)) return;
  if (__atomic_load_n(&m->owner, __ATOMIC_RELAXED) == t) lk_panic_c("同一个任务在 lock 块里又锁了同一个 Mutex，会永远等下去");
  bool front = false;       // 被叫醒过、又没抢到：排回队首
  for (;;) {
    for (int i = 0; i < LK_MUTEX_SPIN; i++) {
      if (!__atomic_load_n(&m->owner, __ATOMIC_RELAXED) && lk_mutex_try(m, t)) return;
      lk_cpu_relax();
    }
    pthread_mutex_lock(&m->mu);
    __atomic_add_fetch(&m->nwait, 1, __ATOMIC_SEQ_CST);
    if (lk_mutex_try(m, t)) {
      __atomic_sub_fetch(&m->nwait, 1, __ATOMIC_SEQ_CST);
      pthread_mutex_unlock(&m->mu);
      return;
    }
    // 别的任务拿着锁（这时调度器一定已经启动了）：排队挂起，解锁的一方叫醒我们以后回去重新抢
    lk_mwaiter w = { t, lk_wait_begin(t), NULL };
    if (front) {
      w.next = m->head;
      m->head = &w;
      if (!m->tail) m->tail = &w;
    } else {
      if (m->tail) m->tail->next = &w; else m->head = &w;
      m->tail = &w;
    }
    lk_park_mu(&m->mu);
    front = true;
  }
}

static void __attribute__((unused)) lk_mutex_unlock(lk_mutex* m) {
  __atomic_store_n(&m->owner, NULL, __ATOMIC_SEQ_CST);
  if (__atomic_load_n(&m->nwait, __ATOMIC_SEQ_CST) == 0) return;
  pthread_mutex_lock(&m->mu);
  lk_mwaiter* w = m->head;
  if (!w) {
    // 正要排队的那个还没挂上（它拿着 mu 时我们进不来），或者它已经自己抢到了
    pthread_mutex_unlock(&m->mu);
    return;
  }
  // 等待者在它自己的栈上，解开 mu 以后它就可能醒来离开，所以先取出要用的
  m->head = w->next;
  if (!m->head) m->tail = NULL;
  __atomic_sub_fetch(&m->nwait, 1, __ATOMIC_SEQ_CST);
  lk_task* t = w->t;
  bool ok = lk_claim(t, w->tok);
  pthread_mutex_unlock(&m->mu);
  if (ok) lk_ready(t);
}

// ---------- Chan[T] ----------
// 无界队列，元素按字节存放（类型相关的部分由生成的 lk_send_* / lk_recv_* / lk_drop_* 负责）。
// rc 是持有者个数：recv 在队列为空时等待，直到有新值，或者除自己以外的持有者都放手（rc == 1），或者通道被 close 了。
// close 以后不能再 send（panic）；队列里剩下的值照样能 recv 出来，取完以后 recv 得到 None。
// 等着的任务挂在通道的等待者链表上。select 在每个通道上各挂一个等待者，它们共用任务的同一个等待编号，
// 先抢到编号的一方（send、放手、定时器）叫醒它，其余的作废。通道的锁只保护几行代码，不会在锁里睡眠。
typedef struct lk_waiter {
  lk_task* t;
  int64_t tok;
  void* out;                // send 把值直接放到这里
  int idx;                  // 是 select 的第几个通道
  bool linked;
  struct lk_waiter* prev;
  struct lk_waiter* next;
} lk_waiter;

typedef struct lk_chan {
  int64_t rc;
  pthread_mutex_t mu;
  char* buf;
  int64_t esz, head, len, cap;
  lk_waiter* wq_head;
  lk_waiter* wq_tail;
  bool closed;
} lk_chan;

static lk_chan* __attribute__((unused)) lk_chan_new(size_t esz) {
  lk_chan* ch = (lk_chan*)lk_alloc(sizeof(lk_chan));
  ch->rc = 1;
  ch->esz = (int64_t)(esz ? esz : 1);
  pthread_mutex_init(&ch->mu, NULL);
  return ch;
}

static void lk_wq_push(lk_chan* ch, lk_waiter* w) {
  w->linked = true;
  w->next = NULL;
  w->prev = ch->wq_tail;
  if (ch->wq_tail) ch->wq_tail->next = w; else ch->wq_head = w;
  ch->wq_tail = w;
}

static void lk_wq_unlink(lk_chan* ch, lk_waiter* w) {
  if (!w->linked) return;
  w->linked = false;
  if (w->prev) w->prev->next = w->next; else ch->wq_head = w->next;
  if (w->next) w->next->prev = w->prev; else ch->wq_tail = w->prev;
}

static void __attribute__((unused)) lk_chan_retain(lk_chan* ch) {
  pthread_mutex_lock(&ch->mu);
  ch->rc++;
  pthread_mutex_unlock(&ch->mu);
}

// 放手；返回是否是最后一个持有者（是的话由调用者释放剩下的值和队列本身）。
// 只剩一个持有者时，叫醒所有等着的任务，让它们重新检查是不是“都结束了”
static bool __attribute__((unused)) lk_chan_release(lk_chan* ch) {
  lk_task* woke = NULL;
  pthread_mutex_lock(&ch->mu);
  int64_t left = --ch->rc;
  if (left == 1) {
    while (ch->wq_head) {
      lk_waiter* w = ch->wq_head;
      lk_wq_unlink(ch, w);
      if (lk_claim(w->t, w->tok)) {
        w->t->fired = -3;
        w->t->next = woke;
        woke = w->t;
      }
    }
  }
  pthread_mutex_unlock(&ch->mu);
  while (woke) {
    lk_task* t = woke;
    woke = t->next;
    lk_ready(t);
  }
  return left == 0;
}

// 叫醒所有等着的任务，让它们重新检查是不是“都结束了”（锁着 ch->mu 时调用），被叫醒的串成链表返回
static lk_task* lk_chan_wake_all_locked(lk_chan* ch) {
  lk_task* woke = NULL;
  while (ch->wq_head) {
    lk_waiter* w = ch->wq_head;
    lk_wq_unlink(ch, w);
    if (lk_claim(w->t, w->tok)) {
      w->t->fired = -3;
      w->t->next = woke;
      woke = w->t;
    }
  }
  return woke;
}

// 声明不会再有值了：等着的 recv 取完队列里剩下的值后得到 None。可以重复调用
static void __attribute__((unused)) lk_chan_close(lk_chan* ch) {
  pthread_mutex_lock(&ch->mu);
  lk_task* woke = ch->closed ? NULL : lk_chan_wake_all_locked(ch);
  ch->closed = true;
  pthread_mutex_unlock(&ch->mu);
  while (woke) {
    lk_task* t = woke;
    woke = t->next;
    lk_ready(t);
  }
}

static void __attribute__((unused)) lk_chan_send(lk_chan* ch, const void* v) {
  pthread_mutex_lock(&ch->mu);
  if (ch->closed) {
    pthread_mutex_unlock(&ch->mu);
    lk_panic_c("向已经 close 的通道 send");
  }
  // 有人等着：值直接交给它（作废的等待者顺手摘掉）
  while (ch->wq_head) {
    lk_waiter* w = ch->wq_head;
    lk_wq_unlink(ch, w);
    if (lk_claim(w->t, w->tok)) {
      memcpy(w->out, v, (size_t)ch->esz);
      w->t->fired = w->idx;
      pthread_mutex_unlock(&ch->mu);
      lk_ready(w->t);
      return;
    }
  }
  if (ch->len == ch->cap) {
    // 扩容时把环形缓冲区摊平
    int64_t nc = ch->cap * 2 + 8;
    char* nb = (char*)lk_alloc((size_t)(nc * ch->esz));
    for (int64_t i = 0; i < ch->len; i++) {
      memcpy(nb + i * ch->esz, ch->buf + ((ch->head + i) % ch->cap) * ch->esz, (size_t)ch->esz);
    }
    lk_free(ch->buf);
    ch->buf = nb;
    ch->cap = nc;
    ch->head = 0;
  }
  memcpy(ch->buf + ((ch->head + ch->len) % ch->cap) * ch->esz, v, (size_t)ch->esz);
  ch->len++;
  pthread_mutex_unlock(&ch->mu);
}

// 不等待：有值就取出最早的一个
static bool lk_chan_take_locked(lk_chan* ch, void* out) {
  if (ch->len == 0) return false;
  memcpy(out, ch->buf + ch->head * ch->esz, (size_t)ch->esz);
  ch->head = (ch->head + 1) % ch->cap;
  ch->len--;
  return true;
}

static bool __attribute__((unused)) lk_chan_take(lk_chan* ch, void* out) {
  pthread_mutex_lock(&ch->mu);
  bool ok = lk_chan_take_locked(ch, out);
  pthread_mutex_unlock(&ch->mu);
  return ok;
}

static void __attribute__((unused)) lk_chan_free(lk_chan* ch) {
  pthread_mutex_destroy(&ch->mu);
  lk_free(ch->buf);
  lk_free(ch);
}

// select 挂起以后由调度循环调用：先解定时器堆的锁（有定时器时），再从后往前解通道的锁。
// 这些数据在挂起的任务的栈上；任务被叫醒以后第一件事是按顺序锁上这些通道，会卡在 ord[0] 上，
// 所以解开 ord[0] 之前它们都不会变
typedef struct { lk_chan** ord; int m; pthread_mutex_t* tmu; } lk_sel_locks;

static void lk_sel_after(void* p) {
  lk_sel_locks* a = (lk_sel_locks*)p;
  lk_chan** ord = a->ord;
  int m = a->m;
  if (a->tmu) {
    lk_tsan_take(a->tmu);
    pthread_mutex_unlock(a->tmu);
  }
  for (int i = m - 1; i >= 0; i--) {
    lk_tsan_take(&ord[i]->mu);
    pthread_mutex_unlock(&ord[i]->mu);
  }
}

// select：等到 chs 里任意一个有值，取出放进 outs[i] 并返回 i；所有通道都结束了（除自己以外的持有者都放手或者 close 了、
// 队列也空了）返回 -2；timeout_ms >= 0 且到时还没有值返回 -1。
// 同时用到的通道按地址顺序上锁（重复的只锁一次），不会和别的 select 互相卡住
static int __attribute__((unused)) lk_select(lk_chan** chs, void** outs, int n, int64_t timeout_ms) {
  lk_chan* ord[n + 1];
  int m = 0;
  for (int i = 0; i < n; i++) {
    int j = m;
    bool dup = false;
    for (int k = 0; k < m; k++) if (ord[k] == chs[i]) dup = true;
    if (dup) continue;
    while (j > 0 && (uintptr_t)ord[j - 1] > (uintptr_t)chs[i]) { ord[j] = ord[j - 1]; j--; }
    ord[j] = chs[i];
    m++;
  }
  lk_waiter ws[n + 1];
  int64_t deadline = timeout_ms >= 0 ? lk_mono_ns() + timeout_ms * 1000000 : -1;
  for (;;) {
    for (int k = 0; k < m; k++) pthread_mutex_lock(&ord[k]->mu);
    bool alive = false;
    for (int i = 0; i < n; i++) {
      if (lk_chan_take_locked(chs[i], outs[i])) {
        for (int k = m - 1; k >= 0; k--) pthread_mutex_unlock(&ord[k]->mu);
        return i;
      }
      if (chs[i]->rc > 1 && !chs[i]->closed) alive = true;
    }
    int r = 0;
    if (!alive) r = -2;
    else if (deadline >= 0 && lk_mono_ns() >= deadline) r = -1;
    if (r != 0) {
      for (int k = m - 1; k >= 0; k--) pthread_mutex_unlock(&ord[k]->mu);
      return r;
    }
    lk_task* t = lk_self();
    int64_t tok = lk_wait_begin(t);
    for (int i = 0; i < n; i++) {
      ws[i] = (lk_waiter){ .t = t, .tok = tok, .out = outs[i], .idx = i };
      lk_wq_push(chs[i], &ws[i]);
    }
    lk_sel_locks a = { ord, m, NULL };
    if (deadline >= 0) {
      lk_theap* h = lk_timer_lock(t);
      lk_timer_set_locked(h, t, deadline, tok);
      a.tmu = &h->mu;
    }
    if (a.tmu) lk_tsan_give(a.tmu);
    for (int k = 0; k < m; k++) lk_tsan_give(&ord[k]->mu);
    lk_park(lk_sel_after, &a);
    // 醒了：把还挂着的等待者摘掉
    for (int k = 0; k < m; k++) pthread_mutex_lock(&ord[k]->mu);
    for (int i = 0; i < n; i++) lk_wq_unlink(chs[i], &ws[i]);
    for (int k = m - 1; k >= 0; k--) pthread_mutex_unlock(&ord[k]->mu);
    if (t->fired >= 0) return t->fired;
    if (t->fired == -1) return -1;
    // -3：有通道只剩自己一个持有者了，或者被 close 了，回去重新检查
  }
}

static bool __attribute__((unused)) lk_chan_recv(lk_chan* ch, void* out) {
  return lk_select(&ch, &out, 1, -1) >= 0;
}
#endif  // 可选部分（二）

#endif
