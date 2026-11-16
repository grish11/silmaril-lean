module

public import tests.wasm.auto2.KernelBench.Proofs.Adler
public import tests.wasm.auto2.KernelBench.Proofs.Elem
public import tests.wasm.auto2.KernelBench.Proofs.Tuple
public import tests.wasm.auto2.KernelBench.Proofs.Tuple2

@[expose] public section

/-!
# Kernel-checked memory cases of the front-end benchmark

Proofs in `tests.wasm.auto2.KernelBench.Proofs.Adler`: `adlerSum8O2_equiv` (Binaryen `-O2` of
the Adler-32 8-way step, every profile) and `adlerSum8Mutant_not_refines`, both by kernel
evaluation over `Silmaril.Wasm.Auto2.Kernel` (round 2 of `docs/projects/wasm-binaryen-tooling.md`, kernel track).

`tests.wasm.auto2.KernelBench.Proofs.Elem` (pass 2): `elemTable_refs`, a 256-entry table with a
40-function element segment instantiated in the kernel through `tableInitLoopK`.

`tests.wasm.auto2.KernelBench.Proofs.Tuple` (pass 2): Binaryen `-O2` with tuple-typed locals and
`tuple.extract`, read by `wat3b!` and kernel-checked equivalent to its source
(`pairO2_equiv_use`, `pairO2_equiv_swap`).

`tests.wasm.auto2.KernelBench.Proofs.Tuple2` (pass 3): Binaryen `-Os` printed from its IR, with
`tuple.extract` of calls, read by `wat3b!` (`pair2Os_lowered`) and kernel-checked equivalent to
its source (`pair2Os_equiv_first`, `pair2Os_equiv_second`, `pair2Os_equiv_mid`).
-/
