module

public import tests.wasm.auto2.SummBench.Defs
public import Silmaril.Wasm.Auto2.Calls.Thms

/-!
# The summaries benchmark: kernel-checked verdicts

Each proved case is `ModEquiv` at **every** profile and for both front-end relations, by kernel
evaluation of the check on the unrolled summaries (`Silmaril.Wasm.Auto2.Summ.modEquiv_of_fnCheckU`)
or on the summaries with inlined calls (`Silmaril.Wasm.Auto2.Calls.modEquiv_of_fnCheckC`). Each
refuted case replays the counterexample of `wasm-check` on the verified interpreter
(`wasm_diff_refute`).

Not here: `memsum4` against its `-O3` output. The modules have a memory, whose kernel
instantiation does not finish (round 3, `Silmaril.Proofs.Wasm.Auto.FrontBenchX.Proved`); the tool
proves it by the compiled checker (sound by `Silmaril.Wasm.Auto2.Calls.checkEquivC_proved`, trusting
the compiler).

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.SummBench

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Auto.Front
open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded (profile)
open Silmaril.Wasm.Verify (refOracle)
open Silmaril.Wasm.Auto2.Summ (defFuel modEquiv_of_fnCheckU)
open Silmaril.Wasm.Auto2.Calls (modEquiv_of_fnCheckC)
open Silmaril.Wasm.Auto.Bridge (rel_refl)

/-! ## Loops with constant trip counts -/

/-- `sum8` is equivalent to its Binaryen `-O3` output (both loops unrolled). -/
theorem sum8O3_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P sum8 sum8O3 0 :=
  modEquiv_of_fnCheckU (fuel := defFuel) (rel_refl R) (by decide +kernel)

/-- `sum8` is equivalent to `x * 28`. -/
theorem sum8Closed_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P sum8 sum8Closed 0 :=
  modEquiv_of_fnCheckU (fuel := defFuel) (rel_refl R) (by decide +kernel)

/-- `x ^ 4` by a loop is `(x * x) * (x * x)`. -/
theorem pow4_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P pow4 pow4Straight 0 :=
  modEquiv_of_fnCheckU (fuel := defFuel) (rel_refl R) (by decide +kernel)

/-- The four-division loop is equivalent to its Binaryen `-O3` output, traps included. -/
theorem divSum4O3_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P divSum4 divSum4O3 0 :=
  modEquiv_of_fnCheckU (fuel := defFuel) (rel_refl R) (by decide +kernel)

/-- `sum8` with one iteration missing returns `21` on `1`, where `sum8` returns `28`. -/
theorem sum8Mutant_not_refines :
    ¬ ModRefines Rel.eq.toProp (profile refOracle) sum8Mutant sum8 0 := by
  wasm_diff_refute [Val.i32 1]

/-! ## Calls -/

/-- `sumsq` (two calls of a callee that counts its calls in a global) is equivalent to its
Binaryen `-O3` output (the calls inlined). -/
theorem sumsqO3_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P calls callsO3 0 :=
  modEquiv_of_fnCheckC (fuel := defFuel) (rel_refl R) (by decide +kernel)

/-- `mean` (a call of a callee that divides by its second argument, here `2`) is equivalent to
its Binaryen `-O3` output (a shift). -/
theorem meanO3_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P calls callsO3 1 :=
  modEquiv_of_fnCheckC (fuel := defFuel) (rel_refl R) (by decide +kernel)

/-- `ratio` (a call that traps when `b = 0`) is equivalent to its Binaryen `-O3` output, traps
included. -/
theorem ratioO3_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P calls callsO3 2 :=
  modEquiv_of_fnCheckC (fuel := defFuel) (rel_refl R) (by decide +kernel)

/-- `sumsq` is equivalent to the same code inlined by hand. -/
theorem sumsqInlined_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P calls callsInlined 0 :=
  modEquiv_of_fnCheckC (fuel := defFuel) (rel_refl R) (by decide +kernel)

/-- `ratio` is equivalent to the same code inlined by hand. -/
theorem ratioInlined_equiv (R : Rel) (P : Profile) : ModEquiv R.toProp P calls callsInlined 2 :=
  modEquiv_of_fnCheckC (fuel := defFuel) (rel_refl R) (by decide +kernel)

/-- Counting one call instead of two: `1` instead of `2` on `(0, 0)`. -/
theorem sumsqMutant_not_refines :
    ¬ ModRefines Rel.eq.toProp (profile refOracle) callsMutant calls 0 := by
  wasm_diff_refute [Val.i32 0, Val.i32 0]

/-- A division that cannot trap does not refine one that traps on `b = 0` (`Rel.eq`). -/
theorem ratioMutant_not_refines :
    ¬ ModRefines Rel.eq.toProp (profile refOracle) callsMutant calls 2 := by
  wasm_diff_refute [Val.i32 0, Val.i32 0]

end Silmaril.Wasm.Auto2.SummBench
