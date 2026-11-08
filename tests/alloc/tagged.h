// 测试用的分配器（tools/test.lark 用 -include 加进来）：检查运行时和生成的代码只通过 LK_MALLOC / LK_REALLOC / LK_FREE
// 申请和释放内存。每块前面放一个标记，LK_REALLOC 和 LK_FREE 收到没有标记的指针（C 库的 malloc 给的、或者已经释放过的）
// 就报错退出；反过来，C 库的 free 收到这里给出的指针，也会因为地址不是块的开头而被 C 库发现。
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>

#define LK_TAGGED_MAGIC 0x4c41524b414c4c43ull

static void* lk_tagged_malloc(size_t n) {
  uint64_t* p = malloc(n + 16);  // 16 字节的头，后面的内存仍然按 16 对齐
  if (!p) return NULL;
  p[0] = LK_TAGGED_MAGIC;
  p[1] = n;
  return p + 2;
}

static uint64_t* lk_tagged_head(void* q, const char* who) {
  uint64_t* p = (uint64_t*)q - 2;
  if (p[0] != LK_TAGGED_MAGIC) {
    fprintf(stderr, "tagged.h：%s 收到的指针不是 LK_MALLOC 给出的（或者已经释放过）\n", who);
    _exit(99);
  }
  return p;
}

static void* lk_tagged_realloc(void* q, size_t n) {
  if (!q) return lk_tagged_malloc(n);
  uint64_t* p = realloc(lk_tagged_head(q, "LK_REALLOC"), n + 16);
  if (!p) return NULL;
  p[1] = n;
  return p + 2;
}

static void lk_tagged_free(void* q) {
  if (!q) return;
  uint64_t* p = lk_tagged_head(q, "LK_FREE");
  p[0] = 0;
  free(p);
}

#define LK_MALLOC(n) lk_tagged_malloc(n)
#define LK_REALLOC(p, n) lk_tagged_realloc((p), (n))
#define LK_FREE(p) lk_tagged_free(p)
