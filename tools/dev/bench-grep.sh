#!/bin/sh
# lgrep 和系统 grep 的速度对比：sh tools/dev/bench-grep.sh（先 make apps A=lgrep；make bench-grep 会自动做）。
# 输入是 compiler/、std/、runtime/ 的源码重复 200 遍拼成的大文件 build/bench/big.txt（约 1.2 亿字节，第一次运行时生成）。
# 每个模式两边都用 -c 只数行数（不让终端输出影响时间），各跑 RUNS 次（默认 3）取最短的秒数；两边的行数不一样时报出来。
# grep 用 LC_ALL=C（按字节比较，和 lgrep 一样）。
cd "$(dirname "$0")/../.." || exit 1
G=apps/lgrep/build/lgrep
RUNS=${RUNS:-3}
if [ ! -x "$G" ]; then echo "没有 $G：先运行 make apps A=lgrep"; exit 1; fi
BIG=build/bench/big.txt
if [ ! -f "$BIG" ]; then
  mkdir -p build/bench
  i=0
  while [ $i -lt 200 ]; do cat compiler/*.lark std/*.lark runtime/*.h; i=$((i+1)); done > "$BIG"
fi
T=$(mktemp -d)

# best 输出文件 命令…：跑 RUNS 次，标准输出留在文件里，打印最短的秒数
best() {
  out=$1; shift
  b=""
  k=0
  while [ $k -lt "$RUNS" ]; do
    /usr/bin/time -p "$@" > "$out" 2> "$T/time"
    s=$(awk '/^real/{print $2}' "$T/time")
    b=$(awk -v a="$b" -v s="$s" 'BEGIN{ if (a == "" || s + 0 < a + 0) print s; else print a }')
    k=$((k+1))
  done
  echo "$b"
}

fail=0
printf '%-26s %10s %8s %8s %8s\n' "模式" "行数" "grep" "lgrep" "倍数"
row() {
  flags=$1; pat=$2
  g=$(best "$T/g" env LC_ALL=C grep -E $flags -- "$pat" "$BIG")
  l=$(best "$T/l" "$G" $flags -- "$pat" "$BIG")
  ng=$(cat "$T/g"); nl=$(cat "$T/l")
  ratio=$(awk -v g="$g" -v l="$l" 'BEGIN{ if (g + 0 == 0) print "-"; else printf "%.2f", l / g }')
  printf '%-26s %10s %7ss %7ss %7sx\n' "$flags $pat" "$nl" "$g" "$l" "$ratio"
  if [ "$ng" != "$nl" ]; then echo "  ↑ 行数不一样：grep 是 $ng"; fail=1; fi
}
row -c 'fn [a-z_]+\('
row -ci 'err'
row -c 'zzzz_not_there'
row -c '[0-9]+\.[0-9]+'
row -c '^pub fn'
row -vc '^ *$'
row -c 'TODO|FIXME|lk_[a-z]+_lock'
echo "（倍数 = lgrep 的时间 / grep 的时间，小于 1 是 lgrep 快；文件 $(ls -l "$BIG" | awk '{print $5}') 字节，每项取 $RUNS 次里最短的）"
rm -rf "$T"
exit $fail
