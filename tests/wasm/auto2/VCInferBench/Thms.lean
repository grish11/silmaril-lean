module

public import tests.wasm.auto2.VCInferBench.Proofs.Sum
meta import Silmaril.Wasm.Auto2.VCInfer.Defs
meta import tests.wasm.auto2.VCInferBench.Defs
meta import Silmaril.WasmSpec.SumTo.Defs

/-!
# The `vcinfer` benchmark: results

`tests.wasm.auto2.VCInferBench.Proofs.Sum`: for each new program shape the search of
`Silmaril.Wasm.Auto2.VCInfer` picks a candidate (the `#guard`s below pin which), its conditions are
proved by `vcgen4` and the fixed tactic (`vc_tri` for `sum`, `vc_simp` for `max`), and the pairs
are equivalent at every profile for every reflexive relation:

* `sum` (`Silmaril.WasmSpec.SumTo`) against `sum-tmp`, `sum-decfirst`, `sum-copy`
  (`sumTmp_equiv`, `sumDecFirst_equiv`, `sumCopy_equiv`);
* `sum-decfirst` and `sum-copy` against their Binaryen `-O3` (`sumDecFirstO3_equiv`,
  `sumCopyO3_equiv`), and `sum-tmp` against `sum-copy` (`sumTmpCopy_equiv`): both contracts
  inferred;
* `max` (`Silmaril.WasmSpec.Max`, an `if`) against `max-select`, and `max-select` against `max-le`
  (`maxSelect_equiv`, `maxSelectLe_equiv`).

* `sum` against `sum-up`, a counting-up loop (`sumUp_equiv`), through the second template of
  `sumI` (`a = triBV i ∧ i ≤ n₀`, variant `n₀ - i`).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCInferBench

open Silmaril.Wasm.Auto2.VCInfer

/-- The side the search finds for export `0` of `m` (for the guards below). -/
meta def sideStr (I : InferFun) (m : Silmaril.Wasm.Module) : String :=
  match side? I m 0 with
  | some (.lib i) => s!"lib {i}"
  | some (.inferred (some c) _) => s!"{c.t} {c.n} {c.a} {c.guard}"
  | some (.inferred none _) => "none"
  | none => "-"

#guard sideStr sumI sumTmp = "0 0 2 false"
#guard sideStr sumI sumDecFirst = "0 0 1 false"
#guard sideStr sumI sumCopy = "0 2 1 true"
#guard sideStr sumI sumDecFirstO3 = "0 0 1 false"
#guard sideStr sumI sumCopyO3 = "0 0 1 true"
#guard sideStr sumI sumUp = "1 2 1 false"
#guard sideStr sumI Silmaril.WasmSpec.SumTo.program = "lib 0"
#guard sideStr maxI maxSelect = "none"
#guard sideStr maxI maxLe = "none"

end Silmaril.Wasm.Auto2.VCInferBench

/--
info: 'Silmaril.Wasm.Auto2.VCInferBench.sumCopy_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCInferBench.sumCopy_equiv

/--
info: 'Silmaril.Wasm.Auto2.VCInferBench.sumDecFirstO3_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCInferBench.sumDecFirstO3_equiv

/--
info: 'Silmaril.Wasm.Auto2.VCInferBench.maxSelectLe_equiv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.VCInferBench.maxSelectLe_equiv
