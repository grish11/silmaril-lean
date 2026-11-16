module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.ConstructorValues.Defs
import Mathlib.Tactic

public section

namespace Silmaril.Proofs.Logic.TypeTheory.CIC.ConstructorTagLaws

open Silmaril.Logic.TypeTheory.CIC.SetSemantics
open Silmaril.Logic.SetTheory

universe u

private theorem orderedPair_ne_empty (x y : ZFSet.{u}) : ZFSet.pair x y ≠ ∅ := by
  intro heq
  have hmember : ({x} : ZFSet.{u}) ∈ ZFSet.pair x y := by simp [ZFSet.pair]
  have hfalse : ({x} : ZFSet.{u}) ∈ (∅ : ZFSet.{u}) := heq ▸ hmember
  exact ZFSet.notMem_empty _ hfalse

/-- Constructor argument tuple codes retain every argument and its position. -/
theorem argumentTuple_injective : Function.Injective argumentTuple.{u} := by
  intro values
  induction values with
  | nil =>
      intro other heq
      cases other with
      | nil => rfl
      | cons a rest => exact (orderedPair_ne_empty a (argumentTuple rest) heq.symm).elim
  | cons a rest ih =>
      intro other heq
      cases other with
      | nil => exact (orderedPair_ne_empty a (argumentTuple rest) heq).elim
      | cons b tail =>
          have hpair : a = b ∧ argumentTuple rest = argumentTuple tail := ZFSet.pair_inj.mp heq
          exact congrArg₂ List.cons hpair.1 (ih hpair.2)

/-- Distinct constructor tags or argument tuples have distinct actual set values. -/
theorem constructorValue_inj {index other : ℕ} {arguments values : List ZFSet.{u}} :
    constructorValue index arguments = constructorValue other values ↔ index = other ∧ arguments = values := by
  simp only [constructorValue, ZFSet.pair_inj, numeral_inj, argumentTuple_injective.eq_iff]

end Silmaril.Proofs.Logic.TypeTheory.CIC.ConstructorTagLaws
