#!/bin/sh
# 在电脑上模拟“没有操作系统”：Lark 程序只带运行时的核心、加 LK_BARE 编译，平台函数和内存池由 plat.c 提供。
# 再用 nm 检查 Lark 程序的目标文件只用到 C 库里不碰系统的部分（内存和字符串函数、snprintf、strtod、数学函数），
# 最后链接、运行。用法（在仓库根目录）：sh examples/bare/run.sh <lark1> [cc] [CFLAGS]
L="$1"
CC="${2:-cc}"
FLAGS="${3:--std=gnu11 -O2 -Wall}"
B=build/bare
mkdir -p "$B" || exit 1
"$L" examples/bare/main.lark -o "$B/main.c" || exit 1
grep -q '#define LK_CORE 1' "$B/main.c" || { echo "没有只带运行时的核心"; exit 1; }
$CC $FLAGS -include examples/bare/bare.h -Iruntime -c "$B/main.c" -o "$B/main.o" || exit 1
$CC $FLAGS -Iexamples/bare -c examples/bare/plat.c -o "$B/plat.o" || exit 1
# 目标文件里没有定义、要从外面找的符号（macOS 的符号前面多一个 _）
nm -u "$B/main.o" | sed -e 's/^ *U //' -e 's/^_//' > "$B/undef.txt"
bad=$(grep -E '^(_*f?printf(_chk)?|fwrite|fputc|fputs|puts|putchar|fflush|fopen|fclose|fread|fseek|ftell|_*stdoutp|_*stderrp|stdout|stderr|exit|_exit|abort|atexit|clock_gettime|time|clock|getentropy|arc4random_buf|getpid|fork|pipe|dup2|read|write|close|waitpid|system|popen|pclose|malloc|calloc|realloc|free|pthread_.*|flockfile|funlockfile)$' "$B/undef.txt")
if [ -n "$bad" ]; then
  echo "Lark 程序的目标文件用到了操作系统或 stdio："
  echo "$bad"
  exit 1
fi
echo "目标文件只用到 C 库里不碰系统的部分"
$CC "$B/main.o" "$B/plat.o" -lm -o "$B/main" || exit 1
"./$B/main"
echo "退出码 $?"
