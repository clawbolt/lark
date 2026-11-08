// llua 用到的几个 C 函数：数字按 printf 的格式转成字符串（Lua 自己也是这么做的，结果才能一模一样），以及 CPU 时间。
// 返回的字符串放在静态缓冲区里，Lark 那边会马上复制一份。
#include <stdio.h>
#include <string.h>
#include <time.h>
#include <math.h>

static char llua_buf[512];

// tostring 用的写法：%.14g，看起来像整数时补上 ".0"（Lua 5.4 的 lua_Number2str 加 tostringbuff）
const char* llua_num_str(double x) {
  snprintf(llua_buf, sizeof llua_buf, "%.14g", x);
  if (strspn(llua_buf, "-0123456789") == strlen(llua_buf)) strcat(llua_buf, ".0");
  return llua_buf;
}

// string.format 的一项，spec 形如 "%5.2f"；整数的格式在转换字母前补上 ll
const char* llua_fmt_num(const char* spec, double x) {
  snprintf(llua_buf, sizeof llua_buf, spec, x);
  return llua_buf;
}

const char* llua_fmt_int(const char* spec, long n) {
  char f[64];
  size_t k = strlen(spec);
  if (k == 0 || k > 32) return "";
  memcpy(f, spec, k - 1);
  f[k - 1] = 'l';
  f[k] = 'l';
  f[k + 1] = spec[k - 1];
  f[k + 2] = 0;
  snprintf(llua_buf, sizeof llua_buf, f, (long long)n);
  return llua_buf;
}

double llua_clock(void) { return (double)clock() / CLOCKS_PER_SEC; }
