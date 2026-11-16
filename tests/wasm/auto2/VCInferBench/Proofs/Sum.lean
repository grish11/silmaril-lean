module

public import Silmaril.Wasm.Auto2.VCInfer.Thms
public import tests.wasm.auto2.VCInferBench.Defs

/-!
# The `vcinfer` benchmark: inferred contracts and equivalences

Each new program's contract is `inferEntry` of the candidate the search picks (checked by the
`#guard`s of `tests.wasm.auto2.VCInferBench.Thms`), with its conditions proved by `vcgen4` and the
fixed tactic of its `InferFun` (`vc_tri` for `sum`, `vc_simp` for `max`): the same tactic for every
program. The equivalences are `modEquiv_of_infer` with `vcEquivWith` evaluated by the kernel.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.VCInferBench

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Auto2.VCGen Silmaril.Wasm.Auto2.VCLib Silmaril.Wasm.Auto2.VCInfer
open Silmaril.Wasm.Auto.Front (ModEquiv)

set_option maxRecDepth 100000

/-- The inferred contract of `sum-tmp` (accumulator local 2). -/
def sumTmpE : Silmaril.Wasm.Auto2.VCBridge.VcEntry :=
  inferEntry sumI (some ⟨0, 0, 2, false⟩) sumTmpFunc
    (by show AllValid sumFns (genFunc (sumI.specOf _) sumTmpFunc libFuel); vc_tri)

/-- The inferred contract of `sum-decfirst`. -/
def sumDecFirstE : Silmaril.Wasm.Auto2.VCBridge.VcEntry :=
  inferEntry sumI (some ⟨0, 0, 1, false⟩) sumDecFirstFunc
    (by show AllValid sumFns (genFunc (sumI.specOf _) sumDecFirstFunc libFuel); vc_tri)

/-- The inferred contract of `sum-copy` (counter local 2, accumulator local 1, guard). -/
def sumCopyE : Silmaril.Wasm.Auto2.VCBridge.VcEntry :=
  inferEntry sumI (some ⟨0, 2, 1, true⟩) sumCopyFunc
    (by show AllValid sumFns (genFunc (sumI.specOf _) sumCopyFunc libFuel); vc_tri)

/-- The inferred contract of Binaryen's `-O3` of `sum-decfirst`. -/
def sumDecFirstO3E : Silmaril.Wasm.Auto2.VCBridge.VcEntry :=
  inferEntry sumI (some ⟨0, 0, 1, false⟩) sumDecFirstO3Func
    (by show AllValid sumFns (genFunc (sumI.specOf _) sumDecFirstO3Func libFuel); vc_tri)

/-- The inferred contract of Binaryen's `-O3` of `sum-copy`. -/
def sumCopyO3E : Silmaril.Wasm.Auto2.VCBridge.VcEntry :=
  inferEntry sumI (some ⟨0, 0, 1, true⟩) sumCopyO3Func
    (by show AllValid sumFns (genFunc (sumI.specOf _) sumCopyO3Func libFuel); vc_tri)

/-- The inferred contract of `sum-up` (counting-up template: counter local 2, accumulator local 1). -/
def sumUpE : Silmaril.Wasm.Auto2.VCBridge.VcEntry :=
  inferEntry sumI (some ⟨1, 2, 1, false⟩) sumUpFunc
    (by show AllValid sumFns (genFunc (sumI.specOf _) sumUpFunc libFuel); vc_tri)

/-- The inferred contract of `max-select`. -/
def maxSelectE : Silmaril.Wasm.Auto2.VCBridge.VcEntry :=
  inferEntry maxI none maxSelectFunc
    (by show AllValid {} (genFunc (maxI.specOf _) maxSelectFunc libFuel); vc_simp)

/-- The inferred contract of `max-le`. -/
def maxLeE : Silmaril.Wasm.Auto2.VCBridge.VcEntry :=
  inferEntry maxI none maxLeFunc
    (by show AllValid {} (genFunc (maxI.specOf _) maxLeFunc libFuel); vc_simp)

variable {P : Numerics.Profile} {R : Behaviour Val → Behaviour Val → Prop}

/-- The contracts check `SumTo`'s program and `sum-tmp`. -/
theorem sumTmp_check : Silmaril.Wasm.Auto2.VCEquiv.vcEquivWith (libEntry sumI 0) sumTmpE Silmaril.WasmSpec.SumTo.program sumTmp 0 = true := by
  decide +kernel

/-- **`SumTo`'s program and `sum-tmp` are equivalent**, every profile, every reflexive relation. -/
theorem sumTmp_equiv (hR : ∀ b, R b b) : ModEquiv R P Silmaril.WasmSpec.SumTo.program sumTmp 0 :=
  modEquiv_of_infer (e₁ := libEntry sumI 0) (e₂ := sumTmpE) hR sumI (derives_libEntry sumI 0)
    (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) sumTmp_check

/-- The contracts check `SumTo`'s program and `sum-decfirst`. -/
theorem sumDecFirst_check : Silmaril.Wasm.Auto2.VCEquiv.vcEquivWith (libEntry sumI 0) sumDecFirstE Silmaril.WasmSpec.SumTo.program sumDecFirst 0 = true := by
  decide +kernel

/-- **`SumTo`'s program and `sum-decfirst` are equivalent**, every profile, every reflexive relation. -/
theorem sumDecFirst_equiv (hR : ∀ b, R b b) : ModEquiv R P Silmaril.WasmSpec.SumTo.program sumDecFirst 0 :=
  modEquiv_of_infer (e₁ := libEntry sumI 0) (e₂ := sumDecFirstE) hR sumI (derives_libEntry sumI 0)
    (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) sumDecFirst_check

/-- The contracts check `SumTo`'s program and `sum-copy`. -/
theorem sumCopy_check : Silmaril.Wasm.Auto2.VCEquiv.vcEquivWith (libEntry sumI 0) sumCopyE Silmaril.WasmSpec.SumTo.program sumCopy 0 = true := by
  decide +kernel

/-- **`SumTo`'s program and `sum-copy` are equivalent**, every profile, every reflexive relation. -/
theorem sumCopy_equiv (hR : ∀ b, R b b) : ModEquiv R P Silmaril.WasmSpec.SumTo.program sumCopy 0 :=
  modEquiv_of_infer (e₁ := libEntry sumI 0) (e₂ := sumCopyE) hR sumI (derives_libEntry sumI 0)
    (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) sumCopy_check

/-- The contracts check `sum-decfirst` and its Binaryen `-O3`. -/
theorem sumDecFirstO3_check : Silmaril.Wasm.Auto2.VCEquiv.vcEquivWith (sumDecFirstE) sumDecFirstO3E sumDecFirst sumDecFirstO3 0 = true := by
  decide +kernel

/-- **`sum-decfirst` and its Binaryen `-O3` are equivalent**, every profile, every reflexive relation. -/
theorem sumDecFirstO3_equiv (hR : ∀ b, R b b) : ModEquiv R P sumDecFirst sumDecFirstO3 0 :=
  modEquiv_of_infer (e₁ := sumDecFirstE) (e₂ := sumDecFirstO3E) hR sumI (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) sumDecFirstO3_check

/-- The contracts check `sum-copy` and its Binaryen `-O3`. -/
theorem sumCopyO3_check : Silmaril.Wasm.Auto2.VCEquiv.vcEquivWith (sumCopyE) sumCopyO3E sumCopy sumCopyO3 0 = true := by
  decide +kernel

/-- **`sum-copy` and its Binaryen `-O3` are equivalent**, every profile, every reflexive relation. -/
theorem sumCopyO3_equiv (hR : ∀ b, R b b) : ModEquiv R P sumCopy sumCopyO3 0 :=
  modEquiv_of_infer (e₁ := sumCopyE) (e₂ := sumCopyO3E) hR sumI (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) sumCopyO3_check

/-- The contracts check `sum-tmp` and `sum-copy` (both inferred). -/
theorem sumTmpCopy_check : Silmaril.Wasm.Auto2.VCEquiv.vcEquivWith (sumTmpE) sumCopyE sumTmp sumCopy 0 = true := by
  decide +kernel

/-- **`sum-tmp` and `sum-copy` (both inferred) are equivalent**, every profile, every reflexive relation. -/
theorem sumTmpCopy_equiv (hR : ∀ b, R b b) : ModEquiv R P sumTmp sumCopy 0 :=
  modEquiv_of_infer (e₁ := sumTmpE) (e₂ := sumCopyE) hR sumI (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) sumTmpCopy_check

/-- The contracts check `SumTo`'s program and `sum-up`. -/
theorem sumUp_check :
    Silmaril.Wasm.Auto2.VCEquiv.vcEquivWith (libEntry sumI 0) sumUpE Silmaril.WasmSpec.SumTo.program sumUp 0 =
      true := by
  decide +kernel

/-- **`SumTo`'s program and `sum-up` (a counting-up loop) are equivalent**, every profile, every
reflexive relation. -/
theorem sumUp_equiv (hR : ∀ b, R b b) : ModEquiv R P Silmaril.WasmSpec.SumTo.program sumUp 0 :=
  modEquiv_of_infer (e₁ := libEntry sumI 0) (e₂ := sumUpE) hR sumI (derives_libEntry sumI 0)
    (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) sumUp_check

/-- The contracts check `Max`'s program and `max-select`. -/
theorem maxSelect_check : Silmaril.Wasm.Auto2.VCEquiv.vcEquivWith (libEntry maxI 0) maxSelectE Silmaril.WasmSpec.Max.program maxSelect 0 = true := by
  decide +kernel

/-- **`Max`'s program and `max-select` are equivalent**, every profile, every reflexive relation. -/
theorem maxSelect_equiv (hR : ∀ b, R b b) : ModEquiv R P Silmaril.WasmSpec.Max.program maxSelect 0 :=
  modEquiv_of_infer (e₁ := libEntry maxI 0) (e₂ := maxSelectE) hR maxI (derives_libEntry maxI 0)
    (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) maxSelect_check

/-- The contracts check `max-select` and `max-le` (both inferred). -/
theorem maxSelectLe_check : Silmaril.Wasm.Auto2.VCEquiv.vcEquivWith (maxSelectE) maxLeE maxSelect maxLe 0 = true := by
  decide +kernel

/-- **`max-select` and `max-le` (both inferred) are equivalent**, every profile, every reflexive relation. -/
theorem maxSelectLe_equiv (hR : ∀ b, R b b) : ModEquiv R P maxSelect maxLe 0 :=
  modEquiv_of_infer (e₁ := maxSelectE) (e₂ := maxLeE) hR maxI (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩)
    (.inr ⟨rfl, rfl, rfl, rfl, rfl⟩) maxSelectLe_check

end Silmaril.Wasm.Auto2.VCInferBench
