#!/bin/sh
# 抓热点：sh tools/dev/profile.sh 秒数 命令 [参数…]
# 在后台运行命令，用 macOS 的 sample 采样指定的秒数，打印两张表：
#   1. 自身时间：样本落在哪些函数里（sample 的 “Sort by top of stack”），前 25 行。CPU 算得慢的程序看这张
#   2. 等待：落在锁、kevent 上的样本是从哪些 lk_ / f_ 函数调过去的（tools/sample-callers.awk）。服务器看这张
# 完整的采样留在 build/profile.sample。命令要比采样时间跑得久；跑不了那么久时用 make profile-grep 这类
# 把输入重复几遍的写法，或者缩短秒数。
cd "$(dirname "$0")/../.." || exit 1
S=${1:-}
if [ -z "$S" ] || [ $# -lt 2 ]; then echo "用法：sh tools/dev/profile.sh 秒数 命令 [参数…]"; exit 2; fi
shift
mkdir -p build
OUT=build/profile.sample
rm -f "$OUT"
"$@" > /dev/null &
PID=$!
sleep 0.1
if ! kill -0 $PID 2> /dev/null; then echo "命令在采样开始前就结束了：换一个更大的输入"; exit 1; fi
/usr/bin/sample $PID "$S" -file "$OUT" > /dev/null 2>&1
alive=0
kill -0 $PID 2> /dev/null && alive=1
wait $PID 2> /dev/null
if ! grep -q '^Sort by top of stack' "$OUT" 2> /dev/null; then
  echo "没有采到：命令在采样期间结束了。缩短秒数（S=1）或者把输入弄大"
  exit 1
fi
[ $alive = 0 ] && echo "注意：命令在 $S 秒的采样结束前就退出了，样本比预期少"
echo "== 自身时间（样本数，前 25）=="
awk '/^Sort by top of stack/{on = 1; next} on && NF == 0 {exit} on {sub(/^ +/, ""); print}' "$OUT" | awk 'NR <= 25'
echo
echo "== 等待：锁 / kevent 的调用者 =="
w=$(awk -f tools/sample-callers.awk "$OUT" | sort -rn | awk 'NR <= 15')
if [ -n "$w" ]; then echo "$w"; else echo "（没有）"; fi
echo
echo "完整的采样：$OUT"
