#!/bin/sh
# 和真 Redis 逐条比较：同一组命令分别发给 lredis 和 redis-server，回复一条条对比；再用 redis-cli、redis-benchmark 测一下。
# 需要装了 redis-server、redis-cli、redis-benchmark（macOS：brew install redis）。不在 make test1 里，手动运行：
#   cd apps/lredis && lark build && sh tests/compat.sh build/lredis
L=$(cd "$(dirname "$1")" && pwd)/$(basename "$1")
command -v redis-server > /dev/null 2>&1 || { echo "没有 redis-server"; exit 1; }
T=$(mktemp -d)
cd "$T" || exit 1
PL=16391
PR=16392
"$L" --port $PL > lredis.log 2>&1 &
LPID=$!
redis-server --port $PR --save '' --appendonly no > redis.log 2>&1 &
RPID=$!
sleep 0.5

# 每行一条命令；KEYS 的顺序在真 Redis 里不固定，所以只用匹配一个键的模式
cat > cmds.txt <<'CMDS'
PING
PING hello
ECHO "a b"
SET k v
GET k
GET missing
SET k v2 XX GET
SET k2 v NX
SET k2 x NX
SET k3 1 EX 100 GET
TTL k3
SET k3 2 KEEPTTL
TTL k3
SET bad v EX 0
SET bad v EX abc
SET bad v FOO
INCR counter
INCRBY counter 10
DECR counter
DECRBY counter 3
INCR k
SET max 9223372036854775807
INCR max
APPEND k suffix
STRLEN k
MSET m1 a m2 b
MGET m1 m2 missing k
MSET m1
SETNX m1 z
GETSET m1 new
GETDEL m1
EXISTS m1 m2 m2 k
DEL m2 missing
EXPIRE k 50
TTL k
PTTL missing
PERSIST k
TTL k
EXPIRE k abc
TYPE k
TYPE missing
RPUSH list a b c
LPUSH list x y
LRANGE list 0 -1
LRANGE list -2 100
LRANGE list 5 1
LINDEX list 1
LINDEX list -1
LINDEX list 99
LLEN list
LPOP list
RPOP list 2
LPOP list 0
LRANGE list 0 -1
TYPE list
GET list
LPUSH k x
HSET hash f1 v1 f2 v2
HSET hash f1 new f3 v3
HGET hash f1
HGET hash nope
HLEN hash
HGETALL hash
HKEYS hash
HVALS hash
HEXISTS hash f2
HDEL hash f2 nope
HGETALL hash
HSET hash odd
TYPE hash
KEYS hash
KEYS h?sh
KEYS nomatch*
SELECT 0
SELECT 99
NOSUCH a b
GET
DEL list hash k k2 k3 counter max
DBSIZE
CMDS

# 两边都从空的数据库开始，按顺序一条条发给两边，比较每一条的回复（数组回复会有好几行）
"$L" cli -p $PL FLUSHALL > /dev/null
"$L" cli -p $PR FLUSHALL > /dev/null
n=0
same=0
while IFS= read -r line; do
  [ -z "$line" ] && continue
  n=$((n+1))
  a=$(printf "%s\n" "$line" | "$L" cli -p $PL 2>&1)
  b=$(printf "%s\n" "$line" | "$L" cli -p $PR 2>&1)
  if [ "$a" = "$b" ]; then
    same=$((same+1))
  else
    echo "不一样：$line"
    echo "  lredis：$a"
    echo "  redis： $b"
  fi
done < cmds.txt
echo "逐条比较：$same / $n 条和真 Redis 一样"

if command -v redis-cli > /dev/null 2>&1; then
  echo "== redis-cli 连 lredis"
  redis-cli -p $PL SET hello world
  redis-cli -p $PL GET hello
  redis-cli -p $PL RPUSH rl 1 2 3
  redis-cli -p $PL LRANGE rl 0 -1
fi
if command -v redis-benchmark > /dev/null 2>&1; then
  for p in $PL $PR; do
    if [ $p = $PL ]; then echo "== redis-benchmark：lredis"; else echo "== redis-benchmark：真 Redis"; fi
    redis-benchmark -p $p -q -n 50000 -c 50 -t ping,set,get,incr,lpush,lpop
    echo "-- 流水线 16 条"
    redis-benchmark -p $p -q -n 200000 -c 50 -P 16 -t set,get
  done
fi
"$L" cli -p $PL SHUTDOWN
kill $RPID 2> /dev/null
wait 2> /dev/null
cd / && rm -rf "$T"
