#!/usr/bin/env bash
# test.sh ARCH OBJDIR -- serve a directory on 127.0.0.1 with the built darkhttpd (natively or under
# qemu-user) and fetch from it with curl.
. "$(dirname "$0")/../common.sh"
start_test darkhttpd "$1" "$2"
case $ARCH in x86_64) PORT=18381 ;; aarch64) PORT=18382 ;; esac
t=$(mktemp -d); mkdir -p "$t/www/sub"; printf 'hello from darkhttpd on %s\n' "$ARCH" > "$t/www/hello.txt"
head -c 100000 /dev/urandom > "$t/www/sub/blob.bin"
"${RUN[@]}" "$OBJ/darkhttpd" "$t/www" --addr 127.0.0.1 --port $PORT --no-server-id > "$t/log" 2>&1 &
pid=$!
for i in $(seq 50); do curl -s -o /dev/null "http://127.0.0.1:$PORT/" && break; sleep 0.2; done
check "${RUNS}darkhttpd www --addr 127.0.0.1 --port $PORT; curl -s http://127.0.0.1:$PORT/hello.txt" \
  "hello from darkhttpd on $ARCH" "$(curl -s "http://127.0.0.1:$PORT/hello.txt")"
check "curl http://127.0.0.1:$PORT/sub/blob.bin (100000 random bytes): sha256 matches" \
  "$(sha256sum < "$t/www/sub/blob.bin")" "$(curl -s "http://127.0.0.1:$PORT/sub/blob.bin" | sha256sum)"
check "curl -w '%{http_code}' http://127.0.0.1:$PORT/missing" 404 "$(curl -s -o /dev/null -w '%{http_code}' "http://127.0.0.1:$PORT/missing")"
check "curl -r 6-9 http://127.0.0.1:$PORT/hello.txt (range request: status + body)" "206 from" \
  "$(curl -s -r 6-9 -w ' %{http_code}' "http://127.0.0.1:$PORT/hello.txt" | awk '{print $2, $1}')"
check "curl http://127.0.0.1:$PORT/sub/ (directory listing names blob.bin)" 1 "$(curl -s "http://127.0.0.1:$PORT/sub/" | grep -c 'blob.bin')"
kill $pid 2>/dev/null || true; wait $pid 2>/dev/null || true
record "darkhttpd log (first lines)" "$(head -n 5 "$t/log" | tr '\n' ' ')"
rm -rf "$t"
exit $TEST_FAILED
