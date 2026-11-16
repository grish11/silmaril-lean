# x86-64 simulators written in WebAssembly

* `x86/x86-g.wat`, `x86/x86-m.wat`: the run-time simulators. G keeps the machine state in
  globals and M in a memory page. They are generated from `x86/src/*.wat` by `wasm-sim gen-x86`
  and tested against the host CPU (`wasm-sim difftest-insn`, `difftest-fn`). They are **not
  proved**; `Silmaril.Sim.X86Real` quotes them verbatim and proves a first slice of G.
* `x86/tests/`: the functions and contracts of the difftests (`funcs.S`, `cfuncs.c`,
  `contracts.toml`, `specs.txt`).
* `x86/problems/`: x86 functions posed as Wasm problems (see its README).
* `rv64/`: the RV64 simulators. `rv64/parts/*.wat` are assembled by `wasm-sim-rv wat` into
  `rv64/gen/rv64-{g,m}-{base,alu,nosys,full}.wat` (**tested**, not proved);
  `rv64/problems/` holds the RV64 reduction plans and their generated Wasm problems; the
  proved RV64 results are in `Silmaril.Sim.RV64`. `rv64/run-tests.sh` runs the difftests.

The proved route is the certified translator `Silmaril.Sim.X86.G`. Docs:
[Simulators in Wasm](../../docs/projects/wasm-sim.md), [ABI](../../docs/projects/wasm-sim-abi.md),
[reduction](../../docs/projects/wasm-sim-reduction.md). Harness: `tools/wasm-sim`.
