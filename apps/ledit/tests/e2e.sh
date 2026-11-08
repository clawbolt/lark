#!/bin/sh
# ledit 的端到端测试：用 --keys 按键脚本编辑临时文件（不需要终端），检查保存下来的内容、提示和屏幕。每项打印 ok 或 FAIL。
# 用法：在 apps/ledit 里 sh tests/e2e.sh <ledit 的路径>
L="$1"
cd "$(dirname "$0")/.." || exit 1
T=$(mktemp -d)
cd "$T" || exit 1
fail=0
check() {
  if [ "$2" = "$3" ]; then printf 'ok   %s\n' "$1"; else printf 'FAIL %s：想要「%s」，得到「%s」\n' "$1" "$3" "$2"; fail=1; fi
}
keys() { printf '%s' "$1" > k.txt; }
nl='
'

printf 'hello\nworld\n' > f.txt
keys '<End>, there<Down><Home>big <C-s><C-q>'
check save_msg "$("$L" --keys k.txt f.txt)" "已保存 f.txt（2 行）"
check saved "$(cat f.txt)" "hello, there${nl}big world"

keys '第一行<Enter>second<C-s>'
"$L" --keys k.txt new.txt > /dev/null
# 逐字节比较（包括最后的换行）。不用 od：有的机器上 PATH 里的 od 是别的程序
printf '第一行\nsecond\n' > want.txt
if cmp -s new.txt want.txt; then r=same; else r="$(cat new.txt)"; fi
check new_file "$r" same

printf 'q\n' > g.txt
keys 'x<C-q>'
check quit_warn "$("$L" --keys k.txt g.txt)" "有改动没保存：再按一次 Ctrl-Q 不保存退出，Ctrl-S 保存"
check unsaved "$(cat g.txt)" "q"

keys 'abc<C-z><C-s>'
"$L" --keys k.txt g.txt > /dev/null
check undo_save "$(cat g.txt)" "q"

printf '云雀\nab\n' > s.txt
keys '<Down><End>'
check screen "$("$L" --keys k.txt --screen --rows 5 --cols 20 s.txt)" "Ctrl-S 保存  Ctrl-Q 退出  Ctrl-Z 撤销  Ctrl-F 搜索${nl}|云雀${nl}|ab${nl}|~${nl}| s.txt  2 行    2:3 ${nl}|Ctrl-S 保存  Ctrl-Q "

keys '<Nope>'
"$L" --keys k.txt g.txt > /dev/null 2>&1
check bad_script "$?" "2"
"$L" g.txt < /dev/null > /dev/null 2>&1
check not_tty "$?" "2"

# 两万行的文件：在中间打 200 个换行、上下走一千步再保存，看看列表中间插入（每次挪后面所有的行）有多慢
awk 'BEGIN{ for (i = 1; i <= 20000; i++) print "line " i }' > big.txt
s='<PgDn><PgDn><PgDn>'
i=0; while [ $i -lt 200 ]; do s="$s<Enter>"; i=$((i+1)); done
i=0; while [ $i -lt 1000 ]; do s="$s<Down>"; i=$((i+1)); done
keys "$s<C-s>"
"$L" --keys k.txt big.txt > /dev/null
check big_file "$(awk 'END{print NR}' big.txt)" "20200"

cd / && rm -rf "$T"
exit $fail
