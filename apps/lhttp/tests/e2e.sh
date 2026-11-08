#!/bin/sh
# lhttp 的端到端测试：在系统挑的端口上启动服务器，提供 tests/site，用 curl 和 nc 发请求，每项打印 ok 或 FAIL。
# 用法：在 apps/lhttp 里 sh tests/e2e.sh <lhttp 的路径>
L="$1"
cd "$(dirname "$0")/.." || exit 1
ROOT="$PWD/tests/site"
T=$(mktemp -d)
"$L" --port 0 --root "$ROOT" > "$T/srv.log" 2>&1 &
SRV=$!
i=0
while ! grep -q '上提供' "$T/srv.log" 2> /dev/null; do
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
# 状态码 内容类型 正文长度
w() { curl -s -o /dev/null -w '%{http_code} %{content_type} %{size_download}' "$@"; }

check index "$(w "$U/")" "200 text/html; charset=utf-8 61"
check index_body "$(curl -s "$U/" | grep -c 'hello from lhttp')" "1"
check css "$(w "$U/sub/style.css")" "200 text/css; charset=utf-8 21"
check space "$(curl -s "$U/sub/with%20space.txt")" "a b"
check redirect "$(curl -s -o /dev/null -w '%{http_code} %{redirect_url}' "$U/sub")" "301 $U/sub/"
check listing "$(curl -s "$U/sub/" | grep -c '<li>')" "3"
check not_found "$(w "$U/nope")" "404 text/plain; charset=utf-8 14"
check traversal "$(curl -s -o /dev/null -w '%{http_code}' --path-as-is "$U/../tests.lark")" "403"
check head "$(curl -s -I "$U/" | grep -c '^Content-Length: 61')" "1"
check method "$(curl -s -o /dev/null -w '%{http_code}' -X DELETE "$U/")" "405"
check echo "$(curl -s --data-binary 'hello body' "$U/echo")" "hello body"
# 一个连接上依次两个请求（curl 复用连接）
check keepalive "$(curl -s -o /dev/null -o /dev/null -w '%{num_connects}\n' "$U/" "$U/sub/style.css" | tr -d '\n')" "10"
# HTTP/1.0 要保持连接时，回复里必须有 Connection: keep-alive（ab -k 就是这样用的；没有的话客户端会等连接关闭）
check http10_keepalive "$(curl -s -o /dev/null -D - --http1.0 -H 'Connection: keep-alive' "$U/sub/style.css" | tr -d '\r' | grep -ci '^connection: keep-alive$')" "1"
# 把 Last-Modified 原样发回来（浏览器的条件请求）：没改过就是 304
lm=$(curl -s -I "$U/sub/style.css" | tr -d '\r' | sed -n 's/^Last-Modified: //p')
check not_modified "$(curl -s -o /dev/null -w '%{http_code}' -H "If-Modified-Since: $lm" "$U/sub/style.css")" "304"
# 流水线：两个请求一次发过去，两个回复按顺序回来
got=$(printf 'GET /sub/style.css HTTP/1.1\r\nHost: x\r\n\r\nGET /nope HTTP/1.1\r\nHost: x\r\nConnection: close\r\n\r\n' | nc 127.0.0.1 "$P" | grep '^HTTP/1.1' | tr -d '\r' | tr '\n' ',')
check pipeline "$got" "HTTP/1.1 200 OK,HTTP/1.1 404 Not Found,"
# 错误的请求：回 400 并关闭连接
got=$(printf 'BAD\r\n\r\n' | nc 127.0.0.1 "$P" | sed -n '1p' | tr -d '\r')
check bad_request "$got" "HTTP/1.1 400 Bad Request"
# 50 个客户端同时请求
pids=""
for k in $(seq 1 50); do
  curl -s -o /dev/null -w '%{http_code}\n' "$U/sub/style.css" >> "$T/many.txt" &
  pids="$pids $!"
done
wait $pids
check concurrent "$(grep -c '^200$' "$T/many.txt")" "50"

kill $SRV 2> /dev/null
wait $SRV 2> /dev/null
rm -rf "$T"
exit $fail
