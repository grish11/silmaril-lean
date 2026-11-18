#!/bin/bash
# Run time (median of $RUNS wall-clock runs, incl. Wasm compilation) and size of each
# linking/packaging variant on the same workloads: progs/hello (startup) and progs/bench
# (~12M simulated instructions). Needs build.sh, merge.sh, components.sh and the
# wsim-proc binary ($WSIM, default: cargo run).
set -u
cd "$(dirname "$0")/progs"
RUNS=${RUNS:-5}
B=../build
WSIM=${WSIM:-"cargo run -q --release -j 3 --manifest-path ../../../../tools/wasm-sim/Cargo.toml --bin wsim-proc --"}
med() { # command... -> median seconds
  for i in $(seq $RUNS); do
    s=$(date +%s.%N); "$@" >/dev/null 2>&1; e=$(date +%s.%N); echo "$e - $s" | bc
  done | sort -n | sed -n "$(( (RUNS + 1) / 2 ))p"
}
size() { cat "$@" | wc -c; }
printf "%-22s %-5s %10s %10s %9s\n" variant sim hello_s bench_s bytes
for s in mini g m; do
  SIM=$B/x86-$s.wasm
  core="$B/io.wasm $B/mem.wasm $B/sys.wasm $B/stubs.wasm $B/libc.wasm $SIM $B/extrun.wasm $B/loader.wasm"
  row() { printf "%-22s %-5s %10.3f %10.3f %9s\n" "$1" $s "$(med "${@:3}" hello)" "$(med "${@:3}" bench)" "$2"; }
  row rust-host "$(size $SIM)" $WSIM run --sim $s
  row rust-wasm-mem "$(size $SIM $B/mem.wasm)" $WSIM run --sim $s --wasm-mem $B/mem.wasm
  row preload-core "$(size $core)" env WSIM_SIM=$s WSIM_EXT=libc ../run-wasi.sh
  row wasm-merge "$(size $B/merged-$s.wasm)" wasmtime run --dir . $B/merged-$s.wasm
  row wasm-merge-O3 "$(size $B/merged-$s-O3.wasm)" wasmtime run --dir . $B/merged-$s-O3.wasm
  [ -f $B/comp/process-$s.wasm ] && row component-wac "$(size $B/comp/process-$s.wasm)" wasmtime run --dir . $B/comp/process-$s.wasm
done
