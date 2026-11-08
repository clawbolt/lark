#!/bin/sh
# lgit 的端到端测试：在临时目录里 init、add、status、commit、log、diff、branch、checkout、merge，再用真 git 检查仓库、逐字比较差异（没有 git 时跳过）。
# 用法：sh tests/e2e.sh <lgit 的路径>。提交号随时间变，所以输出里的编号换成 <id>（blob 的编号是固定的，保留）。
L="$1"
T=$(mktemp -d)
cd "$T" || exit 1
export GIT_AUTHOR_NAME=测试 GIT_AUTHOR_EMAIL=t@example.com GIT_AUTHOR_DATE="1700000000 +0800"
ids() { sed -e 's/[0-9a-f]\{40\}/<id>/g' -e 's/^[0-9a-f]\{7\} /<id> /' -e 's/ [0-9a-f]\{7\}\]/ <id>]/' -e 's/曾为 [0-9a-f]\{7\}/曾为 <id>/' -e 's/新的提交 [0-9a-f]\{7\}/新的提交 <id>/' -e 's/更新 [0-9a-f]\{7\}\.\.[0-9a-f]\{7\}/更新 <id>..<id>/' -e 's/^Merge: [0-9a-f]\{7\} [0-9a-f]\{7\}$/Merge: <id> <id>/'; }
# 差异里的 index 行：编号换成 <h>（0000000 保留）
hs() { sed -e "s/0000000/@Z@/g" -e "/^index /s/[0-9a-f]\{7\}/<h>/g" -e "s/@Z@/0000000/g"; }

echo "== init"
"$L" init . > /dev/null
"$L" status
echo "== 新建文件"
printf 'hello\n' > a.txt
: > empty.txt
mkdir -p src
printf 'hello\n' > src/b.txt
"$L" status
echo "== add ."
"$L" add .
"$L" status
echo "== commit"
"$L" commit -m "第一次提交" | ids
"$L" status
"$L" ls-tree -r HEAD
echo "== 修改、删除、新建"
printf 'world\n' >> a.txt
rm empty.txt
printf 'x\n' > new.txt
"$L" status
"$L" add a.txt empty.txt
"$L" status
"$L" commit -m "第二次" | ids
"$L" commit -m "空的" 2>&1
echo "== log"
"$L" log --oneline | ids
"$L" log -n 1 | ids
echo "== diff"
printf 'hello\nthere\nworld\n' > a.txt
"$L" diff | hs
"$L" add a.txt
"$L" diff
"$L" diff --cached | hs
"$L" commit -m "第三次" | ids
echo "== 分支"
"$L" branch dev
"$L" checkout dev 2>&1
printf 'dev\n' > dev.txt
"$L" add dev.txt
"$L" commit -m "dev 上的提交" | ids
"$L" branch
"$L" checkout main 2>&1
ls
"$L" diff main dev | hs
"$L" branch -d dev 2>&1
printf 'mine\n' > dev.txt
"$L" checkout dev 2>&1
rm dev.txt
printf 'local\n' >> src/b.txt
"$L" checkout dev 2>&1
"$L" status
"$L" checkout -- src/b.txt
"$L" checkout -b topic 2>&1
"$L" branch
"$L" checkout main 2>&1
"$L" branch -D topic 2>&1 | ids
"$L" checkout main 2>&1
"$L" status
echo "== 真 git 读 lgit 的仓库"
if command -v git > /dev/null 2>&1; then
  git status --porcelain
  git fsck --no-progress 2>&1
  git log --format='%an|%s'
  git branch
  # 差异和真 git 逐字比较（关掉可能影响输出的个人配置）
  same() {
    what="$1"
    shift
    a=$("$L" "$@")
    b=$(git -c core.abbrev=7 -c diff.noprefix=false -c diff.mnemonicPrefix=false -c diff.algorithm=myers --no-pager "$@" --no-color --no-ext-diff 2>&1)
    if [ "$a" = "$b" ]; then
      echo "${what}：和真 git 一样"
    else
      echo "${what}：和真 git 不一样"
      echo "--- lgit"
      echo "$a"
      echo "--- git"
      echo "$b"
    fi
  }
  same "两个分支之间" diff main dev
  { echo "int main() {"; i=1; while [ $i -le 20 ]; do echo "  step $i;"; i=$((i+1)); done; echo "}"; } > long.txt
  "$L" add long.txt
  "$L" commit -m "长文件" > /dev/null
  { echo "int main() {"; i=1; while [ $i -le 20 ]; do
      if [ $i = 3 ]; then echo "  step three;"; elif [ $i != 17 ]; then echo "  step $i;"; fi
      i=$((i+1))
    done; echo "}"; printf 'end'; } > long.txt
  same "工作区的修改" diff
  "$L" add long.txt
  same "暂存的修改" diff --cached
else
  echo "（没有 git，跳过）"
fi
echo "== 合并"
# 用真 git 看暂存区里的冲突（没有 git 时跳过）
porcelain() { if command -v git > /dev/null 2>&1; then git status --porcelain; else echo "（没有 git，跳过）"; fi; }
mkdir "$T/m" && cd "$T/m" || exit 1
"$L" init > /dev/null
printf '1\n2\n3\n4\n5\n6\n7\n8\n' > f.txt
printf 'keep\n' > k.txt
"$L" add .
"$L" commit -m "起点" | ids
"$L" branch side
printf '1\n2\n3\n4\n5\n6\n7\nEIGHT\n' > f.txt
"$L" add f.txt
"$L" commit -m "main 改第 8 行" | ids
"$L" checkout side 2>&1
printf 'ONE\n2\n3\n4\n5\n6\n7\n8\n' > f.txt
printf 'new\n' > s.txt
"$L" add .
"$L" commit -m "side 改第 1 行" | ids
"$L" checkout main 2>&1
"$L" merge side | ids
cat f.txt
ls
"$L" log --oneline | ids
"$L" log -n 1 | ids | sed -n '2p'
"$L" merge side
echo "-- 快进"
"$L" checkout side 2>&1
"$L" merge main | ids
"$L" checkout main 2>&1
echo "-- 冲突"
printf 'ONE\n2\n3\nmain\n5\n6\n7\nEIGHT\n' > f.txt
printf 'keep2\n' > k.txt
"$L" add .
"$L" commit -m "main 改第 4 行" | ids
"$L" checkout side 2>&1
printf 'ONE\n2\n3\nside\n5\n6\n7\nEIGHT\n' > f.txt
rm k.txt
"$L" add .
"$L" commit -m "side 改第 4 行、删掉 k" | ids
"$L" checkout main 2>&1
"$L" merge side > ../mo.txt 2> ../me.txt
echo "退出码 $?"
cat ../mo.txt ../me.txt
cat f.txt
"$L" status
porcelain
"$L" commit -m x 2>&1
"$L" checkout side 2>&1
printf 'ONE\n2\n3\nboth\n5\n6\n7\nEIGHT\n' > f.txt
rm k.txt
"$L" add f.txt k.txt
"$L" status
"$L" commit | ids
"$L" log -n 1 | ids | sed -n '2p'
"$L" status
echo "-- 放弃合并"
"$L" checkout side 2>&1
printf 'x\n' > s.txt
"$L" add s.txt
"$L" commit -m "side 改 s" > /dev/null
"$L" checkout main 2>&1
printf 'y\n' > s.txt
"$L" add s.txt
"$L" commit -m "main 改 s" > /dev/null
"$L" merge side > /dev/null 2>&1
echo "退出码 $?"
"$L" merge --abort
cat s.txt
"$L" status
echo "== 真 git 读合并过的仓库"
if command -v git > /dev/null 2>&1; then
  git status --porcelain
  git fsck --no-progress 2>&1
  git log --first-parent --format='%s'
  git cat-file -p HEAD~1 | grep -c '^parent'
  # merge-file 和真 git 逐字比较（输出和退出码）
  mf() {
    what="$1"
    a=$("$L" merge-file -p o.txt b.txt t.txt; echo "退出码 $?")
    b=$(git merge-file -p o.txt b.txt t.txt; echo "退出码 $?")
    if [ "$a" = "$b" ]; then
      echo "${what}：和真 git 一样"
    else
      echo "${what}：和真 git 不一样"
      echo "--- lgit"
      echo "$a"
      echo "--- git"
      echo "$b"
    fi
  }
  printf '1\n2\n3\n4\n5\n6\n7\n8\n' > b.txt
  printf '1\nTWO\n3\n4\n5\n6\n7\n8\n' > o.txt
  printf '1\n2\n3\n4\n5\n6\nSEVEN\n8\n' > t.txt
  mf "merge-file 不挨着的改动"
  printf '1\n2\n3\nours\n5\n6\n7\n8\n' > o.txt
  printf '1\n2\n3\ntheirs\n5\n6\n7\n8\n' > t.txt
  mf "merge-file 同一行的冲突"
  printf '1\n2\nTHREE\n4\n5\n6\n7\n8\n' > o.txt
  printf '1\n2\n3\nFOUR\n5\n6\n7\n8\n' > t.txt
  mf "merge-file 挨着的两行"
else
  echo "（没有 git，跳过）"
fi
echo "== 可执行权限"
"$L" branch exe
"$L" checkout exe > /dev/null 2>&1
printf '#!/bin/sh\necho hi\n' > run.sh
chmod 755 run.sh
"$L" add run.sh
"$L" commit -m "加一个可执行的脚本" > /dev/null
"$L" ls-tree -r HEAD | grep run.sh | ids
if command -v git > /dev/null 2>&1; then
  git ls-files -s run.sh | ids
else
  echo "（没有 git，跳过）"
fi
"$L" checkout main > /dev/null 2>&1
[ -e run.sh ] || echo "切到 main：run.sh 不在了"
"$L" checkout exe > /dev/null 2>&1
[ -x run.sh ] && echo "切回 exe：run.sh 可以执行"
chmod 644 run.sh
"$L" checkout main > /dev/null 2>&1
"$L" checkout exe > /dev/null 2>&1
[ -x run.sh ] && echo "再切回 exe：执行权限又恢复了"
cd / && rm -rf "$T"
