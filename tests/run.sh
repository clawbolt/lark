#!/bin/sh
# 已由 tools/test.lark（make test1）取代，留着只是备查，可以删掉。
# 用 lark1 跑所有示例和错误用例，和记下来的预期结果逐字比较。
#
#   sh tests/run.sh          比较；有不一致就打印 diff，最后以失败退出（make test1）
#   sh tests/run.sh update   用这次的实际结果重写预期结果，并列出改了哪些（make expect）
#
# 示例 examples/*.lark（另加 examples/modules、examples/multi）：编译、运行，
#   结果是标准输出加标准错误，退出码不为 0 时最后一行记 [退出码 N]；预期结果在 tests/expected/名字.out。
# 警告用例 tests/warn/*.lark：必须编译成功，警告在同目录的 名字.expected。
# 格式化工具 tools/fmt.lark：tests/fmt/名字.lark 的格式化结果在 名字.expected，另外检查源码都已格式化。
# 错误用例 tests/err/*.lark、tests/err1/*.lark、tests/multi：必须编译失败，
#   结果是编译器的报错（文件、行列和信息）；预期结果在同目录的 名字.expected。
#
# 新增示例或用例、或者确认某个输出的变化是对的之后，运行 make expect，再看一遍它列出的文件。
set -u
MODE=${1:-check}
LARK=${LARK:-./build/lark1}
CC=${CC:-cc}
CFLAGS=${CFLAGS:-"-std=gnu11 -O2 -pthread"}
B=build/t
mkdir -p "$B" tests/expected
total=0
fails=0
updated=0
missing=""

fail() {
  fails=$((fails + 1))
}

# compare 名字 实际结果 预期结果
compare() {
  if [ "$MODE" = update ]; then
    if [ ! -f "$3" ] || ! cmp -s "$2" "$3"; then
      cp "$2" "$3"
      echo "已更新 $3"
      updated=$((updated + 1))
    fi
    return
  fi
  if [ ! -f "$3" ]; then
    missing="$missing $3"
    fail
  elif ! cmp -s "$3" "$2"; then
    echo "结果不一致：$1（- 预期，+ 实际）"
    diff -u "$3" "$2" | head -40
    fail
  fi
}

# example 名字 源文件…
example() {
  name=$1
  shift
  total=$((total + 1))
  if ! $LARK "$@" -o "$B/$name.c" 2> "$B/$name.lerr"; then
    echo "编译失败：$name"
    cat "$B/$name.lerr"
    fail
    return
  fi
  if ! $CC $CFLAGS -Iruntime "$B/$name.c" -o "$B/$name" -lm 2> "$B/$name.cerr"; then
    echo "C 编译失败：$name"
    head -20 "$B/$name.cerr"
    fail
    return
  fi
  "./$B/$name" > "$B/$name.out" 2>&1
  code=$?
  if [ $code -ne 0 ]; then echo "[退出码 $code]" >> "$B/$name.out"; fi
  compare "$name" "$B/$name.out" "tests/expected/$name.out"
}

# compile_error 名字 预期结果 源文件…
compile_error() {
  name=$1
  exp=$2
  shift 2
  total=$((total + 1))
  if $LARK "$@" -o "$B/err.c" 2> "$B/err.txt"; then
    echo "没有报错：$name"
    fail
    return
  fi
  compare "$name" "$B/err.txt" "$exp"
}

for f in examples/*.lark; do
  n=${f##*/}
  n=${n%.lark}
  example "$n" "$f"
done
example modules examples/modules/main.lark
example multi examples/multi/main.lark examples/multi/shape.lark

# 警告用例 tests/warn/*.lark：必须编译成功，标准错误（警告）要和同目录的 名字.expected 一致
for f in tests/warn/*.lark; do
  n=${f##*/}
  n=${n%.lark}
  total=$((total + 1))
  if $LARK "$f" -o "$B/warn_$n.c" 2> "$B/warn_$n.err"; then
    compare "$f" "$B/warn_$n.err" "tests/warn/$n.expected"
  else
    echo "编译失败（警告用例应该编译成功）：$f"
    cat "$B/warn_$n.err"
    fail
  fi
done

# 格式化工具 tools/fmt.lark：tests/fmt/名字.lark 格式化后要和 名字.expected 一致，
# 再格式化一次 名字.expected 要得到它自己（幂等）；编译器、标准库、示例的源码也要已经是格式化好的
total=$((total + 1))
if $LARK tools/fmt.lark -o "$B/lark-fmt.c" 2> "$B/fmt.lerr" && $CC $CFLAGS -Iruntime "$B/lark-fmt.c" -o "$B/lark-fmt" 2> "$B/fmt.cerr"; then
  for f in tests/fmt/*.lark; do
    n=${f##*/}
    n=${n%.lark}
    total=$((total + 1))
    "./$B/lark-fmt" --stdout "$f" > "$B/fmt_$n.out" 2>&1
    compare "格式化 $f" "$B/fmt_$n.out" "tests/fmt/$n.expected"
    if [ "$MODE" != update ]; then
      total=$((total + 1))
      "./$B/lark-fmt" --stdout "tests/fmt/$n.expected" > "$B/fmt_$n.again" 2>&1
      compare "再格式化 tests/fmt/$n.expected" "$B/fmt_$n.again" "tests/fmt/$n.expected"
    fi
  done
  if [ "$MODE" != update ]; then
    total=$((total + 1))
    if ! "./$B/lark-fmt" --check compiler/*.lark std/*.lark tools/*.lark examples/*.lark examples/*/*.lark; then
      echo "上面这些源码还没格式化（可以运行 make fmt）"
      fail
    fi
  fi
else
  echo "格式化工具编译失败"
  cat "$B/fmt.lerr"
  [ -f "$B/fmt.cerr" ] && head -20 "$B/fmt.cerr"
  fail
fi

for f in tests/err/*.lark tests/err1/*.lark; do
  compile_error "$f" "${f%.lark}.expected" "$f"
done
compile_error tests/multi tests/multi/bad.expected tests/multi/ok.lark tests/multi/bad.lark

if [ "$MODE" = update ]; then
  echo "预期结果：共 $total 项，更新了 $updated 项"
  exit 0
fi
if [ -n "$missing" ]; then
  echo "缺少预期结果（确认实际结果无误后运行 make expect 生成）：$missing"
fi
if [ $fails -ne 0 ]; then
  echo "失败 $fails 项（共 $total 项）"
  exit 1
fi
echo "全部通过：共 $total 项"
