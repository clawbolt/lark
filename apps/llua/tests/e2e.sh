#!/bin/sh
# llua 的端到端测试：运行 tests/lua 里的脚本，和 tests/expected 里存的输出比较（这些输出是真 Lua 5.4 跑出来的）。
# 用法：在 apps/llua 里 sh tests/e2e.sh build/llua
LLUA=${1:-build/llua}
# 在 apps/llua 里用相对路径运行，报错信息里的文件名（tests/lua/x.lua）才和预期一样
cd "$(dirname "$0")/.." || exit 1
dir=tests
fail=0
for f in "$dir"/lua/*.lua; do
    name=$(basename "$f" .lua)
    want="$dir/expected/$name.out"
    got=$("$LLUA" "$f" 2>&1)
    if [ "$got" = "$(cat "$want")" ]; then
        echo "ok   $name"
    else
        echo "FAIL $name"
        printf '%s\n' "$got" > "/tmp/llua_$name.out"
        diff "$want" "/tmp/llua_$name.out" | sed -n '1,20p'
        fail=1
    fi
done
# 出错时的退出码和错误信息
got=$("$LLUA" -e 'error("boom")' 2>&1)
code=$?
if [ "$code" = 1 ] && [ "$got" = "llua: (command line):1: boom" ]; then echo "ok   error_exit"; else echo "FAIL error_exit：${code} ${got}"; fail=1; fi
got=$("$LLUA" -e 'print(...)' 2>&1)
if [ "$got" = "" ]; then echo "ok   no_args"; else echo "FAIL no_args：${got}"; fail=1; fi
exit $fail
