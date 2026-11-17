#!/bin/bash
# glibc-linked ELF ≡ WASI at runtime (route (a): glibc imports bound to the Wasm glibc-subset).
# * hello-glibc (`puts("Hello, world!")`, gcc -O2 -no-pie, dynamically linked against the
#   host glibc 2.39 = the pin data/glibc/ubuntu_2_39_0ubuntu8_9): on sims mini/G/M via
#   run-glibc.sh vs the hand-written WASI hello (../wasi-bridge/progs/hello-wasi.wat) and vs
#   the static `hello` ELF on run-elf.sh: identical stdout, exit code and lifted WASI events
#   (../wasi-bridge/wasi-trace.awk); vs native execution: stdout and exit code.
# * greet-glibc ARGS (puts, strlen, write, memcpy, memset; exit code = main's value): sims vs
#   native (stdout, exit code); the lifted WASI trace is printed.
set -u
D="$(cd "$(dirname "$0")" && pwd)"; cd "$D/progs"; B=../build; mkdir -p $B
run() { # name cmd... : writes build/NAME.{out,rc,trace}
  local n=$1; shift
  WASMTIME_LOG=wasmtime_wasi=trace "$@" > $B/$n.out 2> $B/$n.log; echo $? > $B/$n.rc
  awk -f ../../wasi-bridge/wasi-trace.awk $B/$n.log > $B/$n.trace
}
same() { cmp -s $B/$1.out $B/$2.out && cmp -s $B/$1.rc $B/$2.rc && { [ -n "${3:-}" ] || cmp -s $B/$1.trace $B/$2.trace; }; }
fail=0
ok() { if same "$@"; then echo "ok   $1 ≡ $2 (stdout, exit $(cat $B/$2.rc)${3:+, no trace})"; else echo "FAIL $1 vs $2"; diff $B/$1.trace $B/$2.trace | head -5; fail=1; fi; }
( cd ../../wasi-bridge/progs && as -o hello.o hello.S && ld -static -Ttext=0x401000 -Tdata=0x402000 -o hello hello.o && rm hello.o )
run hello-wasi wasmtime run ../../wasi-bridge/progs/hello-wasi.wat
( cd ../../wasi-bridge/progs && WASMTIME_LOG=wasmtime_wasi=trace ../run-elf.sh hello > ../../glibc-bridge/build/hello-static.out 2> ../../glibc-bridge/build/hello-static.log; echo $? > ../../glibc-bridge/build/hello-static.rc )
awk -f ../../wasi-bridge/wasi-trace.awk $B/hello-static.log > $B/hello-static.trace
./hello-glibc > $B/hello-native.out; echo $? > $B/hello-native.rc
./greet-glibc ab cde fghij > $B/greet-native.out; echo $? > $B/greet-native.rc
for s in mini g m; do
  run hello-glibc-$s env WSIM_SIM=$s ../run-glibc.sh hello-glibc
  ok hello-glibc-$s hello-wasi
  ok hello-glibc-$s hello-static
  run greet-glibc-$s env WSIM_SIM=$s ../run-glibc.sh greet-glibc ab cde fghij
  ok greet-glibc-$s greet-native notrace
done
ok hello-native hello-wasi notrace
echo "--- lifted WASI trace of hello-glibc (= hello-wasi):"; cat $B/hello-glibc-g.trace
echo "--- lifted WASI trace of greet-glibc ab cde fghij:"; cat $B/greet-glibc-g.trace
exit $fail
