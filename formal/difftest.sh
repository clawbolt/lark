#!/bin/sh
# 对拍 Lean 的所有权检查（formal/DiffGen.lean）和真编译器（build/lark1）。
# 在仓库根目录运行，先 make stage1：
#
#   sh formal/difftest.sh [个数] [种子] [loop|call|defer|clo]
#
# 生成的程序在 build/diff/；两边判断不一样的会打印出来（连同 lark1 的报错），最后以失败退出。
set -u
N=${1:-300}
SEED=${2:-1}
KIND=${3:-loop}
LARK=${LARK:-./build/lark1}
D=build/diff
mkdir -p "$D"
rm -f "$D"/c*.lark
(cd formal && lake build Lark > /dev/null && lake env lean --run DiffGen.lean "$N" "$SEED" "../$D" "$KIND") || exit 1
total=0
bad=0
for f in "$D"/c*.lark; do
  total=$((total + 1))
  want=$(head -1 "$f" | sed 's|^// lean: ||')
  if $LARK -w "$f" -o "$D/out.c" 2> "$D/err.txt"; then got=ok; else got=err; fi
  if [ "$got" != "$want" ]; then
    bad=$((bad + 1))
    echo "不一致：${f}（Lean：${want}，lark1：${got}）"
    if [ "$got" = err ]; then head -3 "$D/err.txt"; fi
  elif [ "$got" = err ] && ! grep -qE "移走|借用|排他" "$D/err.txt"; then
    # 两边都拒绝，但 lark1 不是因为所有权拒绝的：生成器写出了别的错误，这个程序没测到东西
    bad=$((bad + 1))
    echo "原因不同：${f}（lark1 报的不是所有权错误）"
    head -3 "$D/err.txt"
  fi
done
echo "对拍 ${total} 个程序（${KIND}），不一致 ${bad} 个"
[ "$bad" -eq 0 ]
