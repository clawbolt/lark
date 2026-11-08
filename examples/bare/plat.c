// 一块“板子”的支持代码：Lark 程序在 LK_BARE 下需要的五个平台函数，加上一个固定大小的内存池。
// 真的板子上 lark_plat_write 写串口、lark_plat_exit 停机或者复位；这里在电脑上模拟，所以写标准输出、调 _exit。
// 整个程序只有这个文件碰操作系统（run.sh 用 nm 检查 Lark 程序的目标文件）
#include "bare.h"

#include <stdint.h>
#include <string.h>
#include <unistd.h>

void lark_plat_write(int fd, const char* p, size_t n) {
  while (n > 0) {
    ssize_t k = write(fd == 2 ? 2 : 1, p, n);
    if (k <= 0) return;
    p += k;
    n -= (size_t)k;
  }
}

void lark_plat_exit(int code) { _exit(code); }

// 没有实时时钟：墙上时间一直是 0
int64_t lark_plat_now_ns(void) { return 0; }

// 假的计时器：每读一次走 1 微秒
static int64_t ticks;
int64_t lark_plat_mono_ns(void) {
  ticks += 1000;
  return ticks;
}

// 没有硬件随机数：用固定的种子跑 xorshift（真的板子上可以读 ADC 的噪声、计时器的低位）
static uint64_t rng = 0x9E3779B97F4A7C15ull;
void lark_plat_random(void* p, size_t n) {
  unsigned char* b = p;
  for (size_t i = 0; i < n; i++) {
    rng ^= rng << 13;
    rng ^= rng >> 7;
    rng ^= rng << 17;
    b[i] = (unsigned char)rng;
  }
}

// ---------- 内存池 ----------
// 一块静态数组，按 2 的幂分成 16 字节到 1 MiB 的块；释放的块按大小挂回各自的空闲链表，下次同样大小的直接复用。
// 块前面 16 字节记着它的大小档位（后面的内存仍然按 16 对齐）
#define POOL_SIZE (8u << 20)
#define MIN_SHIFT 4
#define MAX_SHIFT 20

static _Alignas(16) unsigned char pool[POOL_SIZE];
static size_t top;
static void* free_list[MAX_SHIFT + 1];

typedef struct {
  size_t shift;
  size_t pad;
} head;

static size_t shift_for(size_t n) {
  size_t s = MIN_SHIFT;
  while (s <= MAX_SHIFT && ((size_t)1 << s) < n) s++;
  return s;
}

void* bare_malloc(size_t n) {
  size_t s = shift_for(n);
  if (s > MAX_SHIFT) return NULL;
  if (free_list[s]) {
    void* p = free_list[s];
    memcpy(&free_list[s], p, sizeof(void*));
    return p;
  }
  size_t need = sizeof(head) + ((size_t)1 << s);
  if (need > POOL_SIZE - top) return NULL;   // 池用完了：运行时会 panic “内存不足”
  head* h = (head*)(pool + top);
  top += need;
  h->shift = s;
  return h + 1;
}

void bare_free(void* p) {
  if (!p) return;
  head* h = (head*)p - 1;
  memcpy(p, &free_list[h->shift], sizeof(void*));
  free_list[h->shift] = p;
}

void* bare_realloc(void* p, size_t n) {
  if (!p) return bare_malloc(n);
  head* h = (head*)p - 1;
  if (n <= ((size_t)1 << h->shift)) return p;
  void* q = bare_malloc(n);
  if (!q) return NULL;
  memcpy(q, p, (size_t)1 << h->shift);
  bare_free(p);
  return q;
}
