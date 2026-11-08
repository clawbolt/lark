// 没有操作系统时编译 Lark 程序的设置：编译生成的 C 时用 -include 加进来（见 run.sh）。
// LK_BARE 让运行时的核心只通过 lark_plat_* 和外界打交道（见 runtime/lark_rt.h 开头），
// 三个 LK_ 宏把内存分配换成 plat.c 里固定大小的内存池
#define LK_BARE 1

#include <stddef.h>

void* bare_malloc(size_t n);
void* bare_realloc(void* p, size_t n);
void bare_free(void* p);

#define LK_MALLOC(n) bare_malloc(n)
#define LK_REALLOC(p, n) bare_realloc((p), (n))
#define LK_FREE(p) bare_free(p)
