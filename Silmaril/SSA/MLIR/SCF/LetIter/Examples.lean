module

public import Silmaril.SSA.MLIR.SCF.LetIter.Thms

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

end Silmaril.MLIR.SCF.LetIter.Examples
