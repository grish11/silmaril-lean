module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Fixture
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.Defs

/-! # Case returns preserve the observation that marks lets inside pairs -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift)
open Semantics (extend)
open CfgEta.TypeCategory (returnRegion_rename)
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer
  (TermObservation SameWith evalRegionWith evalTermWith evalReturnRegion
  extension_same)
open _root_.Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (ValTy)
open scoped Paper.BoundSimulation.Obstruction

universe u v w

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)] {ε : Type w} [HasEff Φ ε] {pe : ε}

set_option linter.concreteInstances false in
theorem caseReturnSeed_same [Observer.UnitPayloadPolicy]
    {observation : TermObservation (α := α) Φ} (unmarked : observation.caseTerm = false)
    {Γ L : List (Ty α)} {r s : Region Φ} (h : Paper.WithCaseReturns.Step pe Γ r s L) :
    SameWith observation Γ r s := by
  cases h with
  | @split A B D a b ha hb _ _ =>
    intro env he
    let S := Silmaril.coprod A B
    have scrutinee : Tm.HasType [S] (.var 0 : Tm Φ) S := .var rfl
    have hleft := ha.rename ((Ren.wk [] S).lift A)
    have hright := hb.rename ((Ren.wk [] S).lift B)
    rw [evalReturnRegion (.case scrutinee hleft hright) he, ← returnRegion_rename, ← returnRegion_rename]
    have typed : ValTy (env 0) (.coprod A B) := he (rfl : At [S] 0 S)
    cases ev : env 0 with
    | atom atom => exact atom.elim
    | unit | pair => simp [evalTermWith, evalRegionWith, unmarked, ev]
    | inl v =>
      rw [ev] at typed
      cases typed with
      | inl hv =>
        simp only [evalTermWith, evalRegionWith, unmarked, Bool.false_eq_true, ↓reduceIte, ev]
        exact (evalReturnRegion hleft (he.extend hv)).symm
    | inr v =>
      rw [ev] at typed
      cases typed with
      | inr hv =>
        simp only [evalTermWith, evalRegionWith, unmarked, Bool.false_eq_true, ↓reduceIte, ev]
        exact (evalReturnRegion hright (he.extend hv)).symm

open scoped Observer.CanonicalUnit in
/-- Marking a let in a pair is compatible with every generator of the
case-return extension of the projection-return and unit-η quotient. -/
theorem caseReturnJoin_same {observation : TermObservation (α := α) Φ} (unmarked : observation.caseTerm = false)
    {Γ L : List (Ty α)} {r s : Region Φ} (h : Paper.WithCaseReturns.Eqv pe Γ r s L) :
    SameWith observation Γ r s :=
  extension_same (fun step => step.elim projectionUnitSeed_same (caseReturnSeed_same unmarked)) h

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
