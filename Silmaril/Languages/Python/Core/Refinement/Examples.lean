module

import Silmaril.Languages.Python.Core.Refinement.Thms
import Silmaril.Languages.Python.Core.Thms

/-! # Python Core behavior comparison examples -/

open Silmaril.Languages.Python.Core Silmaril.Languages.Python.Core.Refinement
open Silmaril.Semantics.Operational

private def largeSum : Body := ⟨.binary .add (.int 18446744073709551615) (.int 2)⟩

example : behaviors .addition largeSum =
    { .finite [.ok 18446744073709551617] (.terminal (.returned (.ok 18446744073709551617))) } :=
  behaviors_of_supported rfl

private def signedDivision : Body := ⟨.binary .floorDiv (.int 7) (.int (-3))⟩

example : behaviors .arithmetic signedDivision = { .finite [.ok (-3)] (.terminal (.returned (.ok (-3)))) } :=
  behaviors_of_supported rfl

example :
    (∃ obs, (comparison .arithmetic).Observes largeSum obs) ∧
    ∀ obs, (comparison .arithmetic).Observes largeSum obs →
      obs = .finite [.ok 18446744073709551617] (.terminal (.returned (.ok 18446744073709551617))) := by
  have features : FeatureLE .addition .arithmetic := fun op _ => by cases op <;> rfl
  have safe : ¬ (comparison .addition).toHasOpSem.UBReachable largeSum :=
    fun ub => ub_iff_unsupported.mp ub rfl
  exact (lift_universal features safe (Q := (· = expected largeSum)) fun obs seen => by
    rwa [behaviors_of_supported (profile := .addition) (body := largeSum) rfl] at seen).2

private def divisionByZero : Body := ⟨.binary .floorDiv (.int 1) (.int 0)⟩
private def zeroError : Observation :=
  .finite [.error .zeroDivisionError] (.terminal (.returned (.error .zeroDivisionError)))

example : (comparison .arithmetic).Observes divisionByZero zeroError :=
  (observes_iff rfl).mpr rfl

example : behaviors .arithmetic divisionByZero = { zeroError } := behaviors_of_supported rfl

example : ¬ (comparison .arithmetic).toHasOpSem.UBReachable divisionByZero :=
  fun ub => ub_iff_unsupported.mp ub rfl

example : (model .addition).NoEntry divisionByZero ∧ ¬ (model .addition).UBReachable divisionByZero :=
  ⟨noEntry_iff.mpr (by decide), model_safe⟩

example : (comparison .addition).initial divisionByZero divisionByZero.start ∧
    (comparison .addition).toHasOpSem.UBReachable divisionByZero ∧
    behaviors .addition divisionByZero = Set.univ :=
  ⟨entry _ _, ub_iff_unsupported.mpr (by decide), behaviors_of_unsupported (by decide)⟩

example : behaviors .arithmetic < behaviors .addition := arithmetic_lt_addition

-- The failing left operand aborts before the addition on the right would run.
private def earlyError : Body :=
  ⟨.binary .floorDiv divisionByZero.value (.binary .add (.int 2) (.int 5))⟩

example : Step earlyError.start none (.raising .zeroDivisionError) :=
  .expr (.left (.compute (.divZero 1)))

example : behaviors ⟨false, true⟩ earlyError = Set.univ :=
  behaviors_of_unsupported (by decide)

example : behaviors .arithmetic earlyError = { zeroError } :=
  behaviors_of_supported rfl
