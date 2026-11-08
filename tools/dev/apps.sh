#!/bin/sh
# 构建 apps/ 下的练手程序：sh tools/dev/apps.sh [名字…]（不给名字时全部构建）。
# 用 build/lark（先 make lark-tool），每个程序的结果在 apps/名字/build/名字，顺便补上执行权限。
cd "$(dirname "$0")/../.." || exit 1
ROOT="$PWD"
if [ ! -x build/lark ]; then echo "没有 build/lark：先运行 make lark-tool"; exit 1; fi
names="$*"
if [ -z "$names" ]; then
  names=$(for d in apps/*/; do [ -f "$d/lark.pkg" ] && basename "$d"; done)
fi
fail=0
for n in $names; do
  if [ ! -f "apps/$n/lark.pkg" ]; then echo "没有这个程序：apps/$n"; fail=1; continue; fi
  if (cd "apps/$n" && LARK_HOME="$ROOT" "$ROOT/build/lark" build > /dev/null); then
    chmod +x "apps/$n/build/$n" 2> /dev/null
    echo "好了  apps/$n/build/$n"
  else
    echo "失败  apps/$n（上面是编译器的报错）"
    fail=1
  fi
done
exit $fail
