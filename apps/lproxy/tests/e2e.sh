#!/bin/sh
# lproxy 的端到端测试：起两个 lhttp 当上游（各自提供一个目录），lproxy 按前缀转过去，用 curl 发请求，每项打印 ok 或 FAIL；
# 最后发 SIGTERM，看它优雅地退出。用法：在 apps/lproxy 里 sh tests/e2e.sh <lproxy 的路径> <lhttp 的路径>
L="$1"
H="$2"
T=$(mktemp -d)
mkdir -p "$T/a/sub" "$T/b/api"
printf 'A\n' > "$T/a/a.txt"
printf 'in sub\n' > "$T/a/sub/x.txt"
printf 'B\n' > "$T/b/api/b.txt"
pids=""
# 起一个服务器，等它打印出带 marker 的那一行，把端口写进变量 $2
start() {
  log="$T/$1.log"
  shift 2
  "$@" > "$log" 2>&1 &
  pids="$pids $!"
  LAST=$!
  i=0
  while ! grep -q '上' "$log" 2> /dev/null; do
    i=$((i+1))
    if [ $i -gt 50 ]; then echo "服务器没有启动：$*"; cat "$log"; kill $pids 2> /dev/null; exit 1; fi
    sleep 0.1
  done
  PORT=$(sed -n 's|.*http://127.0.0.1:\([0-9]*\)/.*|\1|p' "$log" | head -n 1)
}
start a x "$H" --port 0 --root "$T/a"; PA=$PORT
start b x "$H" --port 0 --root "$T/b"; PB=$PORT
# 一个已经关掉的上游：起来拿到端口再关掉
start c x "$H" --port 0 --root "$T/a"; PC=$PORT; kill $LAST; wait $LAST 2> /dev/null
start proxy x "$L" --port 0 --timeout 2000 /api=http://127.0.0.1:$PB /down=http://127.0.0.1:$PC /=http://127.0.0.1:$PA
SRV=$LAST
PP=$PORT
U="http://127.0.0.1:$PP"
fail=0
check() {
  if [ "$2" = "$3" ]; then echo "ok   $1"; else echo "FAIL $1：想要「$3」，得到「$2」"; fail=1; fi
}
code() { curl -s -o /dev/null -w '%{http_code}' "$@"; }

check rules "$(sed -n '1,3p' "$T/proxy.log" | sed "s/:$PA/:A/; s/:$PB/:B/; s/:$PC/:C/" | tr '\n' ',')" "  /api → http://127.0.0.1:B,  /down → http://127.0.0.1:C,  / → http://127.0.0.1:A,"
check root "$(curl -s "$U/a.txt")" "A"
check prefix "$(curl -s "$U/api/b.txt")" "B"
check not_prefix "$(code "$U/apix")" "404"
check nested "$(curl -s "$U/sub/x.txt")" "in sub"
# 上游的 301 原样带回，不跟随
check redirect "$(code "$U/sub")" "301"
check post "$(curl -s --data-binary 'hello body' "$U/echo")" "hello body"
check head "$(curl -s -I "$U/a.txt" | tr -d '\r' | grep -ci '^content-type: text/plain')" "1"
check length "$(curl -s -D - -o /dev/null "$U/a.txt" | tr -d '\r' | grep -ci '^content-length: 2$')" "1"
check bad_gateway "$(code "$U/down/x")" "502"
# 客户端到代理的连接也复用
check keepalive "$(curl -s -o /dev/null -o /dev/null -w '%{num_connects}\n' "$U/a.txt" "$U/api/b.txt" | tr -d '\n')" "10"
check warn_logged "$(grep -c '转发失败' "$T/proxy.log")" "1"

echo "== SIGTERM"
kill -TERM $SRV
wait $SRV
echo "代理退出码 $?"
grep -o '收到 SIGTERM，不再接受新连接，等进行中的请求做完' "$T/proxy.log"
check exit_logged "$(grep -c 'lproxy: 退出$' "$T/proxy.log")" "1"
check refused "$(code "$U/a.txt")" "000"
kill $pids 2> /dev/null
wait 2> /dev/null
rm -rf "$T"
exit $fail
