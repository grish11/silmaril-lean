module

public import Silmaril.Wasm.Auto2.Front2.Thms
public import tests.wasm.auto2.SummBench.Defs
public import tests.wasm.auto.FrontBenchX.Defs
public import Silmaril.WasmSpec.SumTo.Defs

/-!
# Summaries, pass 2: loops with input-dependent trip counts, kernel-checked

`sumO3_equiv`, `sumDoWhile_equiv`, `sumO3DoWhile_equiv` (by `vcEquiv` on the functional contract
`sumFun`) and `sumO3_provev` (through the front end's proving stages).

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

/-- **`sum` is equivalent to its Binaryen `-O3` output**, at every profile: a loop whose trip
count is the input, through the functional contract `sumFun`. -/
theorem sumO3_equiv (R : Rel) (P : Profile) :
    ModEquiv R.toProp P Silmaril.WasmSpec.SumTo.program sumO3 0 :=
  Silmaril.Wasm.Auto2.VCEquiv.modEquiv_of_vcEquiv (Silmaril.Wasm.Auto.Bridge.rel_refl _)
    (F := sumFun) (by decide +kernel)

/-- `sum` is equivalent to its guarded `do … while` form. -/
theorem sumDoWhile_equiv (R : Rel) (P : Profile) :
    ModEquiv R.toProp P Silmaril.WasmSpec.SumTo.program sumDoWhile 0 :=
  Silmaril.Wasm.Auto2.VCEquiv.modEquiv_of_vcEquiv (Silmaril.Wasm.Auto.Bridge.rel_refl _)
    (F := sumFun) (by decide +kernel)

/-- Binaryen's `-O3` of `sum` is equivalent to the `do … while` form. -/
theorem sumO3DoWhile_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P sumO3 sumDoWhile 0 :=
  Silmaril.Wasm.Auto2.VCEquiv.modEquiv_of_vcEquiv (Silmaril.Wasm.Auto.Bridge.rel_refl _)
    (F := sumFun) (by decide +kernel)

/-- The same as `sumO3_equiv`, through the front end's proving stages (stage `vcequiv`). -/
theorem sumO3_provev (R : Rel) (P : Profile) :
    ModEquiv R.toProp P Silmaril.WasmSpec.SumTo.program sumO3 0 := by
  wasm_provev

end Silmaril.Proofs.Wasm.Auto2.Summ2Bench
