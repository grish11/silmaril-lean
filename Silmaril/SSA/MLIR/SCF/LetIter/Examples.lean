module

public import Silmaril.SSA.MLIR.SCF.LetIter.LambdaSSA

/-! # Closed examples with an observable yield and a divergent backedge -/

public section

namespace Silmaril.MLIR.SCF.LetIter.Examples

open Silmaril.Isotope
open Silmaril.Isotope.Institution.Observational (Model Observation noFree iterBeh)
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.Semantics

private def model : Model.{0, 0, 0} Empty 0 where
  α := Empty
  σ := Unit
  instr f := f.elim
  faults f := f.elim
  prim f := f.elim
  bound i := i.elim0

private instance : HasTy Empty (Ty Empty) := ⟨Empty.elim, Empty.elim⟩

private def oneYield : RegionLoop Empty 0 where
  init := .inr .unit
  condition := .bv 0
  afterRegion := .inl (.bv 0)
  parent := .pair (.bv 0) .unit

private def spins : RegionLoop Empty 0 :=
  { oneYield with afterRegion := .inr (.bv 0) }

example : oneYield.WellTyped (τ := Ty Empty) .nil .nil
    (Ty.coprod .unit .unit) .unit (Ty.product .unit .unit) :=
  ⟨.inr .unit, .newest, .inl .newest, .pair .newest .unit⟩

example : Observation.ret () (.pair .unit .unit) () ∈ iterBeh model oneYield.lower := by
  rw [← RegionLoop.observe_eq_iterBeh]
  refine ⟨.inr .unit, (), .unit, (), .inr .unit, ⟨(.inl .unit, ()), ?_, .bv⟩, .pair .bv .unit⟩
  exact .single ⟨.unit, (), .bv, .inl .bv⟩

example : Observation.diverge () ∈ iterBeh model spins.lower := by
  rw [← RegionLoop.observe_eq_iterBeh]
  refine Or.inr ⟨.inr .unit, (), .inr .unit, Or.inl ?_⟩
  refine ⟨fun d => d = (.inr .unit, ()), rfl, ?_⟩
  rintro _ rfl
  exact Or.inr ⟨_, ⟨.unit, (), .bv, .inr .bv⟩, rfl⟩

/-- A fixed continuation can erase a sum tag even though the full answer
distinguishes it. The all-continuations theorem includes the identity test. -/
theorem erasing_continuation :
    Tm.Obs.{0, 0, 0, 0} (.let₁ (.inl .unit) .unit : Tm Empty Empty 0) (.let₁ (.inr .unit) .unit) ∧
      ¬ Tm.Obs.{0, 0, 0, 0} (.inl .unit : Tm Empty Empty 0) (.inr .unit) := by
  constructor
  · have left : Tm.Obs.{0, 0, 0, 0} (.let₁ (.inl .unit) .unit : Tm Empty Empty 0) .unit :=
      obs_letBeta (.inl .unit) .unit (.inl .unit)
    exact left.trans (obs_letBeta (.inr .unit) .unit (.inr .unit)).symm
  · intro h
    have run : Eval model.instr noFree model.bound (.inl .unit) () (.inl .unit) () := .inl .unit
    cases h.eval.mp run

private def repeatBody : Tm Empty Empty 1 := .inr (.bv 0)
private def repeatTerm : Tm Empty Empty 0 := .iter .unit repeatBody
private def stuckTerm : Tm Empty Empty 0 := .abort .unit

/-- The raw native semantics has pairs with identical finite returns and
different divergence observations. -/
example :
    (∀ value, Eval model.instr noFree model.bound repeatTerm () value () ↔
      Eval model.instr noFree model.bound stuckTerm () value ()) ∧
    External.Diverges model.instr noFree model.prim (.term model.bound repeatTerm ()) ∧
    ¬ External.Diverges model.instr noFree model.prim (.term model.bound stuckTerm ()) := by
  refine ⟨fun value => ⟨?_, ?_⟩, ?_, ?_⟩
  · intro run
    cases run with
    | iter _ body =>
        exact (Loop.induction_fixed (motive := fun _ _ _ _ => False)
          (fun done => by cases done) (fun _ _ tail => tail) body).elim
  · intro run
    cases run
  · refine .fold_core (.iter_loop .unit ?_)
    apply External.Diverges.coinduct (fun cfg => cfg = .loop model.bound repeatBody .unit ()) _ rfl
    rintro _ rfl
    exact .core (.loop_step (.inr .bv) rfl)
  · intro h
    cases h.unfold with
    | core h => cases h with
      | abort arg => cases arg.unfold with
        | core h => cases h

end Silmaril.MLIR.SCF.LetIter.Examples
