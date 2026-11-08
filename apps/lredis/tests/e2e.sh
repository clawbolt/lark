#!/bin/sh
# lredis 的端到端测试：在系统挑的端口上启动服务器，用 lredis cli 发命令，最后 SHUTDOWN。
# 用法：sh tests/e2e.sh <lredis 的路径>。和真 Redis 逐条比较见 tests/compat.sh（需要装了 redis-server）。
# 最后两段检查 SIGTERM、SIGINT 能让服务器写日志后退出。
L="$1"
T=$(mktemp -d)
cd "$T" || exit 1
"$L" --port 0 > srv.log 2>&1 &
SRV=$!
i=0
while ! grep -q '上等待连接' srv.log 2> /dev/null; do
  i=$((i+1))
  if [ $i -gt 50 ]; then echo "服务器没有启动"; cat srv.log; exit 1; fi
  sleep 0.1
done
P=$(sed -n 's/.*:\([0-9]*\) 上等待连接.*/\1/p' srv.log)
c() { "$L" cli -p "$P" "$@"; }

echo "== 字符串"
c PING
c SET name lark
c GET name
c SET "with space" "value with space"
c GET "with space"
c GET nope
c INCR n
c INCRBY n 41
c INCR name
c APPEND name -lang
c MSET a 1 b 2
c MGET a b nope
c SET a x NX
c DEL a b nope
c NOPE x y
c GET
echo "== 过期"
c SET t v PX 100
c PTTL t | sed 's/[0-9][0-9]*/<毫秒>/'
sleep 0.3
c GET t
c EXPIRE name 100
c TTL name
echo "== 列表和哈希"
c RPUSH l a b c
c LPUSH l z
c LRANGE l 0 -1
c HSET h f1 v1 f2 v2
c HGETALL h
c LPUSH h x
c TYPE l
c KEYS "[lh]"
echo "== 从标准输入读（一行一条）"
printf 'PING\nECHO "a\\tb"\n\nDBSIZE\n' | c
echo "== 4 个客户端同时 INCR，各 100 次"
pids=""
for k in 1 2 3 4; do
  (j=0; while [ $j -lt 100 ]; do echo "INCR counter"; j=$((j+1)); done) | c > /dev/null &
  pids="$pids $!"
done
wait $pids
c GET counter
echo "== SHUTDOWN"
c SHUTDOWN
wait $SRV
echo "服务器退出码 $?"
c PING 2>&1 | sed 's/：.*/：…/'
# 信号：起一个新的服务器，发信号，看退出码和日志。后台进程本来忽略 SIGINT，notify 以后照样收得到
sig() {
  "$L" --port 0 > srv2.log 2>&1 &
  SRV=$!
  i=0
  while ! grep -q '上等待连接' srv2.log 2> /dev/null; do
    i=$((i+1))
    if [ $i -gt 50 ]; then echo "服务器没有启动"; cat srv2.log; exit 1; fi
    sleep 0.1
  done
  kill -"$1" $SRV
  wait $SRV
  echo "服务器退出码 $?"
  grep -o '收到 SIG[A-Z]*，退出' srv2.log
  rm -f srv2.log
}
echo "== kill -TERM"
sig TERM
echo "== kill -INT"
sig INT
cd / && rm -rf "$T"
