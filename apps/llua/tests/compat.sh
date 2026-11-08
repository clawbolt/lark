#!/bin/sh
# 和真 Lua 对照（手动运行，需要装了 lua 5.4）：
#   1. tests/lua 里每个脚本，llua 和 lua 的输出逐字比较
#   2. bench 里的程序比较运行时间
# 用法：在 apps/llua 里 sh tests/compat.sh build/llua [lua]
# 比较一致后，可以用 sh tests/compat.sh build/llua lua --save 把真 Lua 的输出存成 tests/expected 里的预期结果
LLUA=${1:-build/llua}
LUA=${2:-lua}
# 在 apps/llua 里用相对路径运行，报错信息里的文件名（tests/lua/x.lua）才和预期一样
cd "$(dirname "$0")/.." || exit 1
dir=tests
"$LUA" -v 2>&1 | grep -q "Lua 5.4" || { echo "需要 Lua 5.4：$("$LUA" -v 2>&1)"; exit 1; }
mkdir -p "$dir/expected"
same=0
total=0
for f in "$dir"/lua/*.lua; do
    name=$(basename "$f" .lua)
    total=$((total + 1))
    # 错误信息开头的程序名不同（lua: / llua:），比较前去掉
    want=$("$LUA" "$f" 2>&1 | sed 's/^lua: //')
    got=$("$LLUA" "$f" 2>&1 | sed 's/^llua: //')
    if [ "$want" = "$got" ]; then
        same=$((same + 1))
        echo "一样   $name"
    else
        echo "不一样 $name"
        printf '%s\n' "$want" > /tmp/llua_want.out
        printf '%s\n' "$got" > /tmp/llua_got.out
        diff /tmp/llua_want.out /tmp/llua_got.out | sed -n '1,20p'
    fi
    if [ "$3" = "--save" ]; then "$LUA" "$f" > "$dir/expected/$name.out" 2>&1; fi
done
echo "输出一样的：$same/$total"
echo
echo "运行时间："
for f in bench/*.lua; do
    name=$(basename "$f" .lua)
    s1=$( { /usr/bin/time -p "$LUA" "$f" > /dev/null; } 2>&1 | awk '/^real/ {print $2}')
    s2=$( { /usr/bin/time -p "$LLUA" "$f" > /dev/null; } 2>&1 | awk '/^real/ {print $2}')
    echo "  ${name}：lua ${s1} 秒，llua ${s2} 秒"
done
