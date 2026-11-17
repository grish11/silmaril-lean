#!/bin/sh
# Build the RV64 test programs, difftest every simulator representation against
# qemu-riscv64, run G/M lockstep, the lattice refinement check, and regenerate
# the Wasm problems in problems/ (with their runtime agreement check).
# usage: run-tests.sh [outdir]
set -e
here=$(cd "$(dirname "$0")" && pwd)
out=${1:-/tmp/wsim-rv}
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$here/../../../tools/wasm-sim/target}
nice cargo build -q --release -j 1 --bin wasm-sim-rv --bin wasm-sim --manifest-path "$here/../../../tools/wasm-sim/Cargo.toml"
B=$CARGO_TARGET_DIR/release/wasm-sim-rv   # = cargo run --release -j 3 --bin wasm-sim-rv --
"$here/tests/build.sh" "$out"
LLD=${LLD:-$(command -v ld.lld || ls ~/.elan/toolchains/*/bin/ld.lld | head -1)}
for seed in 1 2 3 4 5; do
  $B gen-rand $seed 3000 "$out/rand$seed.S"
  clang --target=riscv64-linux-gnu -march=rv64im -mabi=lp64 -mno-relax -nostdlib -static --ld-path=$LLD -o "$out/rand$seed" "$out/rand$seed.S"
done
$B difftest "$out/hello" "$out/arith" "$out/memops" "$out/loops" "$out/funcs" "$out/memcall" "$out"/rand[1-5]
$B lattice 100000
$B link-check "$out/hello"
# executable Lean model (optional: set LEAN_DIR to a Silmaril checkout with
# Silmaril.Machine.RiscV.Ext.Machine.Defs built)
LEAN_DIR=${LEAN_DIR:-}
if [ -n "$LEAN_DIR" ] && [ -d "$LEAN_DIR/.lake" ]; then
  $B lean-oracle 20000 "$LEAN_DIR"
  LEAN_DIR=$LEAN_DIR $B lean-prog "$out/hello" "$out/arith" "$out/memops" "$out/loops" "$out/funcs" "$out/memcall"
else echo "skip lean-oracle (LEAN_DIR unset or not a built checkout)"; fi
cd "$here/problems"
export LEAN_DIR
for p in funcs loops arith memcall; do $B reduce $p.toml "$out/$p" $p 50 --lean "$here/../../../Silmaril/WasmSpec"; done
$CARGO_TARGET_DIR/release/wasm-sim dag check */dag.json
# the assembled lattice points, kept in the repository for the Lean side (`wat3!`)
cd "$here"
for s in g m; do for l in base alu nosys full; do $B wat $s $l "gen/rv64-$s-$l.wat"; done; done
git -C "$here" diff --stat -- gen problems
