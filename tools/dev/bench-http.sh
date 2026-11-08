#!/bin/sh
# HTTP 服务的压测：sh tools/dev/bench-http.sh lhttp|lcache [秒数]（默认 10 秒；先 make apps）。
# 在系统挑的端口上启动服务器，用 wrk -t4 -c50 压一个地址，打印每秒请求数和延迟，最后关掉服务器。
#   lhttp：提供 apps/lhttp/tests/site，压首页
#   lcache：先 PUT 一个 100 字节的值，再压 GET 这个键
# 需要 wrk（brew install wrk）。ab 是单线程的，在这里会成为瓶颈，不要用它比较。
cd "$(dirname "$0")/../.." || exit 1
A=${1:-}
D=${2:-10}
case "$A" in
  lhttp) args="--port 0 --root $PWD/apps/lhttp/tests/site" ;;
  lcache) args="--port 0" ;;
  *) echo "用法：sh tools/dev/bench-http.sh lhttp|lcache [秒数]"; exit 2 ;;
esac
B="apps/$A/build/$A"
if [ ! -x "$B" ]; then echo "没有 $B：先运行 make apps A=$A"; exit 1; fi
if ! command -v wrk > /dev/null; then echo "没有 wrk：brew install wrk"; exit 1; fi
T=$(mktemp -d)
"$B" $args > "$T/srv.log" 2>&1 &
SRV=$!
trap 'kill $SRV 2> /dev/null; wait $SRV 2> /dev/null; rm -rf "$T"' EXIT INT TERM
i=0
while ! grep -q 'http://127.0.0.1:' "$T/srv.log" 2> /dev/null; do
  i=$((i+1))
  if [ $i -gt 50 ]; then echo "服务器没有启动："; cat "$T/srv.log"; exit 1; fi
  sleep 0.1
done
P=$(sed -n 's|.*http://127.0.0.1:\([0-9]*\)/.*|\1|p' "$T/srv.log")
U="http://127.0.0.1:$P"
if [ "$A" = lcache ]; then
  awk 'BEGIN{ for (i = 0; i < 100; i++) printf "x" }' > "$T/val"
  curl -s -o /dev/null -X PUT --data-binary @"$T/val" "$U/k/bench"
  U="$U/k/bench"
else
  U="$U/"
fi
echo "$A：wrk -t4 -c50 -d${D}s $U"
wrk -t4 -c50 -d"${D}s" "$U" | awk '/Latency|Requests\/sec|Non-2xx|Socket errors/'
