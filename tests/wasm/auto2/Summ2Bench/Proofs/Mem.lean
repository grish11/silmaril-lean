module

public import Silmaril.Wasm.Auto2.Front2.Thms
public import tests.wasm.auto2.SummBench.Defs
public import tests.wasm.auto.FrontBenchX.Defs
public import Silmaril.WasmSpec.SumTo.Defs

/-!
# Summaries, pass 2: the memory cases, kernel-checked

`memSum4O3_equiv` and `adlerSum8O2_equivV`: `checkAmongV` rewritten by `checkAmongV_eq_K` to the
validation-free, closed-form instance and decided by kernel evaluation.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.Summ2Bench

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Front (Rel ModEquiv)
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.Auto2.SummBench (memSum4 memSum4O3)
open Silmaril.Wasm.Auto.FrontBenchX (adlerSum8 adlerSum8O2)
open Silmaril.Wasm.Auto2.VCEquiv (sumO3 sumDoWhile sumFun vcEquiv)

theorem memSum4_valid : (validate? memSum4).isSome = true := by decide +kernel

theorem memSum4O3_valid : (validate? memSum4O3).isSome = true := by decide +kernel

/-- **`memsum4` is equivalent to its Binaryen `-O3` output**, at every profile: four byte
loads from a data segment in a loop with a constant trip count (unrolled), kernel-checked over
the validation-free, closed-form instance. -/
theorem memSum4O3_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P memSum4 memSum4O3 0 :=
  Silmaril.Wasm.Auto2.Summ2.modEquiv_of_checkAmongV (fuel := Silmaril.Wasm.Auto2.Summ.defFuel) (js := [0])
    (i := 0)
    (Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl
    (by
      rw [Silmaril.Wasm.Auto2.Summ2.checkAmongV_eq_K memSum4_valid memSum4O3_valid]
      decide +kernel)

theorem adlerSum8_valid : (validate? adlerSum8).isSome = true := by decide +kernel

theorem adlerSum8O2_valid : (validate? adlerSum8O2).isSome = true := by decide +kernel

/-- **The Adler-32 8-way step is equivalent to its Binaryen `-O2` output** through the
summaries of pass 2 (kernel-checked over the validation-free instance). -/
theorem adlerSum8O2_equivV (R : Rel) (P : Profile) :
    ModEquiv R.toProp P adlerSum8O2 adlerSum8 0 :=
  Silmaril.Wasm.Auto2.Summ2.modEquiv_of_checkAmongV (fuel := Silmaril.Wasm.Auto2.Summ.defFuel) (js := [0])
    (i := 0)
    (Silmaril.Wasm.Auto.Bridge.rel_refl _) rfl
    (by
      rw [Silmaril.Wasm.Auto2.Summ2.checkAmongV_eq_K adlerSum8O2_valid adlerSum8_valid]
      decide +kernel)

end Silmaril.Proofs.Wasm.Auto2.Summ2Bench
