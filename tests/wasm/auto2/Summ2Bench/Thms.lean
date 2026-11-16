module

public import tests.wasm.auto2.Summ2Bench.Proofs.Mem
public import tests.wasm.auto2.Summ2Bench.Proofs.Loops

/-!
# Summaries, pass 2: kernel-checked benchmark theorems

Regression theorems of `docs/projects/wasm-binaryen-tooling.md`, "Round 2, track summaries (pass 2)", each by
kernel evaluation (proofs in `Silmaril.Proofs.Wasm.Auto2.Summ2Bench.{Mem,Loops}`):

* **memory, through the validation-free instance**: `memSum4O3_equiv` (a loop of four byte loads
  from a data segment, unrolled, against Binaryen `-O3`) and `adlerSum8O2_equivV` (the Adler-32
  8-way step against Binaryen `-O2`), by `checkAmongV` rewritten with `checkAmongV_eq_K`. Pass 1
  of the summaries track proved `memsum4` only in the compiled checker;
* **loops whose trip count depends on the input**, through the functional contract
  `Silmaril.Wasm.Auto2.VCEquiv.sumFun`: `sumO3_equiv` (`Silmaril.WasmSpec.SumTo`'s program against
  its Binaryen `-O3` output), `sumDoWhile_equiv` (against the guarded `do … while` form) and
  `sumO3DoWhile_equiv`, all by `vcEquiv`;
* `sumO3_provev`: the same through the front end's proving stages (`wasm_provev`).

New theorems.
-/

@[expose] public section

/--
info: 'Silmaril.Proofs.Wasm.Auto2.Summ2Bench.memSum4O3_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Proofs.Wasm.Auto2.Summ2Bench.memSum4O3_equiv

/--
info: 'Silmaril.Proofs.Wasm.Auto2.Summ2Bench.sumO3_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Proofs.Wasm.Auto2.Summ2Bench.sumO3_equiv
