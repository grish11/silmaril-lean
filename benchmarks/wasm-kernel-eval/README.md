# Kernel evaluation benchmarks

Benchmarks for `Silmaril.Wasm.KernelEval`; results and analysis in
[docs/projects/wasm-kernel-eval.md](../../docs/projects/wasm-kernel-eval.md).

- `bench.py`: the kernel matrix (`decide +kernel`, `decide`, `run` vs `runRec`, list vs packed
  memory).
- `GenChunks.lean`: after `lake build --wfail +Silmaril.Wasi.Versions.WitImport.KRfl.Defs`,
  `lake env lean --run benchmarks/wasm-kernel-eval/GenChunks.lean N K > Chunk.lean`
  prints a piecewise certificate for `fillSort N` with `K`-step chunks; check it with
  `lake env lean Chunk.lean`.
- `opcode_census.py`: instruction counts of Wasm binaries (core modules and components).
