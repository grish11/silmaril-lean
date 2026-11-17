#!/bin/bash
# ELF ≡ WASI, hello world, at runtime: the static x86-64 ELF `progs/hello` on the simulator
# stack with the syscall → WASI adapter (run-elf.sh), the hand-written WASI p1 program
# `progs/hello-wasi.wat`, and its WASI → syscall → WASI round trip (roundtrip.sh) must give
# byte-identical stdout, the same exit code and the same lifted WASI event list
# (wasi-trace.awk). Also native execution of the ELF (stdout, exit code). Programs: hello
# (write, exit) and cat (read, write, exit_group; stdin = 150 bytes).
set -u
D="$(cd "$(dirname "$0")" && pwd)"; cd "$D/progs"; mkdir -p ../build
IN=../build/stdin.txt; seq 1 40 | head -c 150 > $IN
run() { # name cmd... : writes build/NAME.{out,rc,trace}
  local n=$1; shift
  WASMTIME_LOG=wasmtime_wasi=trace "$@" < $IN > ../build/$n.out 2> ../build/$n.log; echo $? > ../build/$n.rc
  awk -f ../wasi-trace.awk ../build/$n.log > ../build/$n.trace
}
fail=0
for p in hello hello-g cat; do
  q=${p%-g}   # hello-g (the G-fragment hello proved in Lean, Silmaril.Sim.WasiBridge.G) vs hello-wasi
  as -o $p.o $p.S && ld -static -Ttext=0x401000 -Tdata=0x402000 -o $p $p.o && rm $p.o
  ../roundtrip.sh $q-wasi.wat > /dev/null
  ./$p < $IN > ../build/$p-native.out; echo $? > ../build/$p-native.rc
  for s in mini g m; do run $p-elf-$s env WSIM_SIM=$s ../run-elf.sh $p; done
  run $p-wasi wasmtime run $q-wasi.wat
  run $p-roundtrip wasmtime run ../build/rt-$q-wasi.wasm
  W=../build/$p-wasi
  for n in $p-elf-mini $p-elf-g $p-elf-m $p-roundtrip; do
    if cmp -s ../build/$n.out $W.out && cmp -s ../build/$n.rc $W.rc && cmp -s ../build/$n.trace $W.trace
    then echo "ok   $n ≡ $p-wasi (stdout, exit $(cat $W.rc), $(wc -l < $W.trace) WASI events)"
    else echo "FAIL $n vs $p-wasi"; diff ../build/$n.trace $W.trace | head; fail=1; fi
  done
  if cmp -s ../build/$p-native.out $W.out && cmp -s ../build/$p-native.rc $W.rc
  then echo "ok   native $p ≡ $p-wasi (stdout, exit code)"; else echo "FAIL native $p"; fail=1; fi
  echo "--- lifted WASI trace of $p:"; cat $W.trace
done
exit $fail
