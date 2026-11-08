#!/bin/sh
# lcache 的端到端测试：在系统挑的端口上启动服务器，用 curl 发请求，每项打印 ok 或 FAIL。
# 用法：在 apps/lcache 里 sh tests/e2e.sh <lcache 的路径>
L="$1"
cd "$(dirname "$0")/.." || exit 1
T=$(mktemp -d)
"$L" --port 0 > "$T/srv.log" 2>&1 &
SRV=$!
i=0
while ! grep -q ' 上' "$T/srv.log" 2> /dev/null; do
  i=$((i+1))
  if [ $i -gt 50 ]; then echo "服务器没有启动"; cat "$T/srv.log"; kill $SRV 2> /dev/null; exit 1; fi
  sleep 0.1
done
P=$(sed -n 's|.*http://127.0.0.1:\([0-9]*\)/.*|\1|p' "$T/srv.log")
U="http://127.0.0.1:$P"
fail=0
check() {
  if [ "$2" = "$3" ]; then echo "ok   $1"; else echo "FAIL $1：想要「$3」，得到「$2」"; fail=1; fi
}
code() { curl -s -o /dev/null -w '%{http_code}' "$@"; }

check missing "$(code "$U/k/a")" "404"
check put "$(code -X PUT --data-binary 'hello world' "$U/k/a")" "204"
check get "$(curl -s "$U/k/a")" "hello world"
# 二进制的值原样存取
printf 'x\000y\r\nz' > "$T/bin"
check put_bin "$(code -X PUT --data-binary @"$T/bin" "$U/k/bin")" "204"
curl -s "$U/k/bin" > "$T/bin2"
check get_bin "$(cmp -s "$T/bin" "$T/bin2" && echo same)" "same"
check delete "$(code -X DELETE "$U/k/a")" "204"
check deleted "$(code "$U/k/a")" "404"
# 过期：1 秒的 ttl，等 1.5 秒以后没了；再等清理任务跑过，键数也降下来
check put_ttl "$(code -X PUT --data-binary 'soon' "$U/k/t?ttl=1")" "204"
check before_expiry "$(curl -s "$U/k/t")" "soon"
sleep 1.5
check expired "$(code "$U/k/t")" "404"
check put_ttl2 "$(code -X PUT --data-binary 'later' "$U/k/t2?ttl=1")" "204"
sleep 2.5
check swept "$(curl -s "$U/stats" | sed -n 's/.*"keys":\([0-9]*\).*/\1/p')" "1"
check bad_ttl "$(code -X PUT --data-binary 'x' "$U/k/a?ttl=-3")" "400"
check method "$(code -X POST --data-binary 'x' "$U/k/a")" "405"
# 50 个客户端同时写不同的键，再全部读回来（只等这 50 个 curl：不带参数的 wait 会连服务器一起等，永远等不完）
pids=""
for k in $(seq 1 50); do
  curl -s -o /dev/null -X PUT --data-binary "v$k" "$U/k/c$k" &
  pids="$pids $!"
done
wait $pids
got=0
for k in $(seq 1 50); do
  if [ "$(curl -s "$U/k/c$k")" = "v$k" ]; then got=$((got+1)); fi
done
check concurrent "$got" "50"

kill $SRV 2> /dev/null
wait $SRV 2> /dev/null
rm -rf "$T"
exit $fail
