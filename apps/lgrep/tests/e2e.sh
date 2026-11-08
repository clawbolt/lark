#!/bin/sh
# lgrep 的端到端测试：在临时目录里造几个文件跑 lgrep，再在 Lark 自己的源码上和系统的 grep 对比。每项打印 ok 或 FAIL。
# 用法：在 apps/lgrep 里 sh tests/e2e.sh <lgrep 的路径>
G="$1"
cd "$(dirname "$0")/.." || exit 1
ROOT=$(cd ../.. && pwd)
T=$(mktemp -d)
fail=0
check() {
  if [ "$2" = "$3" ]; then printf 'ok   %s\n' "$1"; else printf 'FAIL %s：想要「%s」，得到「%s」\n' "$1" "$3" "$2"; fail=1; fi
}
nl='
'

mkdir -p "$T/d/sub" "$T/d/.hide"
printf 'alpha\nBeta\ngamma 42\ndelta\n' > "$T/d/a.txt"
printf 'one\ntwo beta\n' > "$T/d/sub/b.txt"
printf 'beta\n' > "$T/d/.hide/c.txt"
printf 'beta\n' > "$T/d/.dot"
printf 'x\000beta\n' > "$T/d/sub/z.bin"

check plain "$("$G" eta "$T/d/a.txt")" "Beta"
check number "$("$G" -n 'ma' "$T/d/a.txt")" "3:gamma 42"
check ignore_case "$("$G" -i '^beta' "$T/d/a.txt")" "Beta"
check invert_count "$("$G" -vc a "$T/d/a.txt")" "0"
check classes "$("$G" '\d+' "$T/d/a.txt")" "gamma 42"
check alt "$("$G" 'one|^g' "$T/d/a.txt" "$T/d/sub/b.txt")" "$T/d/a.txt:gamma 42${nl}$T/d/sub/b.txt:one"
check stdin "$(printf 'x\nyes\n' | "$G" y)" "yes"
check stdin_dash "$(printf 'x\nyes\n' | "$G" -n y -)" "2:yes"
# -r：按名字排序，跳过 . 开头的；二进制文件只说有匹配
check recursive "$("$G" -rn beta "$T/d")" "$T/d/sub/b.txt:2:two beta${nl}二进制文件 $T/d/sub/z.bin 有匹配"
check files_only "$("$G" -rli beta "$T/d")" "$T/d/a.txt${nl}$T/d/sub/b.txt${nl}$T/d/sub/z.bin"
E=$(printf '\033')
check color "$("$G" --color mm "$T/d/a.txt")" "ga${E}[1;31mmm${E}[0ma 42"

# 退出码：有匹配 0，没有 1，出错 2
"$G" alpha "$T/d/a.txt" > /dev/null; check exit_match "$?" "0"
"$G" nothing "$T/d/a.txt" > /dev/null; check exit_none "$?" "1"
"$G" 'a[' "$T/d/a.txt" > /dev/null 2>&1; check exit_badpat "$?" "2"
"$G" a "$T/nope.txt" > /dev/null 2>&1; check exit_missing "$?" "2"
"$G" a "$T/d" > /dev/null 2>&1; check exit_dir "$?" "2"
"$G" -q a "$T/d/a.txt" > /dev/null 2>&1; check exit_badflag "$?" "2"

# 和系统的 grep -E 对比（按字节比较，LC_ALL=C），在 Lark 编译器的源码上
same() {
  want=$(LC_ALL=C grep -E $1 -- "$2" "$ROOT"/compiler/*.lark)
  got=$("$G" $1 -- "$2" "$ROOT"/compiler/*.lark)
  if [ "$want" = "$got" ]; then printf 'ok   grep %s %s\n' "$1" "$2"; else printf 'FAIL grep %s %s：和 grep 的结果不一样\n' "$1" "$2"; fail=1; fi
}
same -n 'fn [a-z_]+\('
same -c '^pub fn'
same -n 'TODO|FIXME|XXX'
same -c '[0-9]+\.[0-9]+'
same -ic 'err'
same -vc '^ *$'
same -l 'lk_[a-z]+_lock'
same -n '"[^"]*\\n"'
same -c 'e$'

rm -rf "$T"
exit $fail
