#!/bin/sh
# Component variant: wrap each core module as a component (WIT: ../wit/sim.wit) and compose
# them with wac into one WASI command component per simulator. Run with
#   cd progs && wasmtime run --dir . ../build/comp/process-g.wasm bench
set -eu
cd "$(dirname "$0")"
WIT=../wit/sim.wit
AD=../../wasm-components/adapter
WSIM="cargo run -q --release -j 3 --manifest-path ../../../tools/wasm-sim/Cargo.toml --bin wsim-proc --"
O=build/comp; mkdir -p $O
comp() { # core.wasm name world keep-ifaces [adapter]
  $WSIM componentize "build/$1.wasm" "$O/$2.core.wasm" "$4"
  wasm-tools component embed $WIT --world "$3" "$O/$2.core.wasm" -o "$O/$2.emb.wasm"
  if [ -n "${5:-}" ]; then
    wasm-tools component new "$O/$2.emb.wasm" --adapt wasi_snapshot_preview1="$AD/wasi_snapshot_preview1.$5.wasm" -o "$O/$2.wasm"
  else
    wasm-tools component new "$O/$2.emb.wasm" -o "$O/$2.wasm"
  fi
}
comp mem mem memory mem
comp sys sys syscalls sys reactor
comp stubs nd undef-zero nd
comp libc libc foreign-library ffi reactor
comp extrun extrun extrun state,isa,ext-range
comp loader loader loader "" command
for s in g m; do
  comp x86-$s core-$s simulator state,isa
  for f in libc; do
    wac compose -o $O/process-$s.wasm \
      --dep wsim:mem=$O/mem.wasm --dep wsim:sys=$O/sys.wasm --dep wsim:nd=$O/nd.wasm \
      --dep wsim:core=$O/core-$s.wasm --dep wsim:ffi=$O/$f.wasm --dep wsim:extrun=$O/extrun.wasm \
      --dep wsim:loader=$O/loader.wasm ../wit/process.wac
  done
done
ls -l $O/process-*.wasm
