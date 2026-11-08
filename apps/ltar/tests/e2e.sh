#!/bin/sh
# ltar 的端到端测试：ltar 打的包给系统的 tar 解开，系统的 tar 打的包给 ltar 解开、列出，比较内容、权限位和符号链接；
# 最后是出错、不安全的名字，以及硬链接和修改时间。用法：sh tests/e2e.sh <ltar 的路径>
L="$1"
T=$(mktemp -d)
cd "$T" || exit 1
umask 022
# macOS 的 tar 不要往包里放 ._ 开头的元数据文件
export COPYFILE_DISABLE=1
# 超过 100 字节的路径：要拆成 ustar 的 prefix 和 name 两段
D=$(printf 'd%.0s' $(seq 1 70))
F=$(printf 'f%.0s' $(seq 1 60)).txt
short() { sed -e "s/$D/<长目录>/" -e "s/$F/<长名字>/"; }

mkdir -p src/sub "src/$D"
printf 'hello\n' > src/a.txt
printf '#!/bin/sh\necho hi\n' > src/run.sh
chmod 755 src/run.sh
printf '\000\001\377二进制' > src/sub/bin
: > src/sub/empty
ln -s a.txt src/link
printf 'long\n' > "src/$D/$F"

# 每个文件的权限（ls -l 的前 10 个字符），符号链接写指向哪里
perms() { (cd "$1" && find . | LC_ALL=C sort | while IFS= read -r f; do if [ -L "$f" ]; then echo "$f -> $(readlink "$f")"; else echo "$f $(ls -ld "$f" | cut -c1-10)"; fi; done); }
# 两个目录的内容、权限、符号链接都一样时打印“一样”，否则打印差别
same() {
  perms "$1" > p1
  perms "$2" > p2
  if diff -r "$1" "$2" > /dev/null 2>&1 && cmp -s p1 p2; then
    echo "一样"
  else
    echo "不一样：$1 和 $2"
    diff -r "$1" "$2"
    diff p1 p2
  fi
}

echo "== ltar 打包，系统的 tar 解开"
"$L" c -f a.tar src
mkdir o1 && tar -xf a.tar -C o1 && same src o1/src
echo "== ltar 打包加 gzip，系统的 tar 解开"
"$L" c -zf a.tgz src
gzip -t a.tgz && echo "gzip 校验通过"
mkdir o2 && tar -xzf a.tgz -C o2 && same src o2/src
echo "== 系统的 tar 打包加 gzip，ltar 解开"
tar -czf b.tgz src
"$L" x -f b.tgz -C o3 && same src o3/src
echo "== ltar 打包，ltar 解开"
"$L" x -f a.tar -C o4 && same src o4/src
echo "== 列出"
"$L" t -f a.tar | short
echo "== 列出 -v"
"$L" t -v -f a.tgz | short
echo "== 列出的和系统的 tar 一样"
tar -tf a.tar > t1
"$L" t -f a.tar > t2
cmp -s t1 t2 && echo "ltar 的包：一样"
tar -tzf b.tgz | LC_ALL=C sort > t3
"$L" t -f b.tgz | LC_ALL=C sort > t4
cmp -s t3 t4 && echo "系统的 tar 的包：一样"

echo "== 出错"
"$L" t -f nope.tar
echo "退出码 $?"
printf 'garbage' > bad.tar
"$L" t -f bad.tar
echo "退出码 $?"
"$L" c -f x.tar
echo "退出码 $?"
"$L" x
echo "退出码 $?"
echo "== 不安全的名字"
mkdir w && (cd w && "$L" c -f ../evil.tar ../src/a.txt)
"$L" x -f evil.tar -C o5
echo "退出码 $?"
# 先放一个指向外面的符号链接，再往链接里面写
mkdir -p w2 tgt
ln -s ../tgt w2/up
printf 'x\n' > tgt/x
"$L" c -f evil2.tar w2/up w2/up/x
"$L" x -f evil2.tar -C o6
echo "退出码 $?"
[ -L o6/w2/up ] && [ ! -e o6/tgt/x ] && echo "链接解开了，没有写到链接里面"
echo "== 硬链接和修改时间"
# 系统的 tar 把同一个文件的第二个名字存成硬链接；修改时间要原样设回来（文件和目录都是）
mkdir -p h/d
printf 'same\n' > h/a
ln h/a h/b
touch -t 202001020304.05 h/a
touch -t 201912312359.59 h/d
tar -cf h.tar h
"$L" x -f h.tar -C o7
[ o7/h/a -ef o7/h/b ] && echo "硬链接：是同一个文件"
same_time() { if [ ! "$1" -nt "$2" ] && [ ! "$1" -ot "$2" ]; then echo "$3的修改时间：一样"; else echo "$3的修改时间：不一样"; fi; }
same_time o7/h/a h/a "文件"
same_time o7/h/d h/d "目录"
cd / && rm -rf "$T"
