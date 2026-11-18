#!/usr/bin/env bash
# test.sh ARCH OBJDIR -- run pingpong-server and pingpong-client (natively or both under qemu-user)
# over 127.0.0.1 in one container; record the transcript.
. "$(dirname "$0")/../common.sh"
start_test tcp-pingpong "$1" "$2"
case $ARCH in x86_64) PORT=18391 ;; aarch64) PORT=18392 ;; esac
t=$(mktemp -d)
"${RUN[@]}" "$OBJ/pingpong-server" $PORT > "$t/server.log" 2>&1 &
pid=$!
for i in $(seq 50); do grep -q waiting "$t/server.log" && break; sleep 0.2; done
rc=0; out=$("${RUN[@]}" "$OBJ/pingpong-client" 127.0.0.1 $PORT 5 2>&1) || rc=$?
sleep 0.5; kill $pid 2>/dev/null || true; wait $pid 2>/dev/null || true
check "${RUNS}pingpong-server $PORT & ${RUNS}pingpong-client 127.0.0.1 $PORT 5: exit status, pong count" "0 5" "$rc $(grep -c "received 'pong'" <<<"$out")"
record "client transcript" "$(printf %s "$out" | tr '\n' '|')"
record "server transcript" "$(tr '\n' '|' < "$t/server.log")"
check "server reports 5 rounds" 1 "$(grep -c 'closed after 5 ping/pong rounds' "$t/server.log")"
rm -rf "$t"
exit $TEST_FAILED
