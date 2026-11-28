module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Soundness
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Beta.Constructors.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithProjectionReturnsAndUnitEta.Defs

/-! # The pair sequence and mixed update have distinct observations
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.DeBruijn (lift liftN)
open Silmaril.Isotope.LambdaSSA.Semantics (extend extend_rename)
open scoped Paper.BoundSimulation.Obstruction
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.Observer (Env EnvTy Result)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.Observer (extended_same)

open Paper.UnaryReturn.Beta.Constructors
open Paper.UnaryReturn.Beta.Constructors.Example (source target update constructor)
open Paper.RetainedLet (returnOnce)

section
open scoped Observer.CanonicalUnit

private def env : Env := fun _ => .inl .unit

private theorem env_typed : EnvTy [source] env := by
  intro i A hi
  cases i with
  | zero => cases Option.some.inj hi; exact .inl .unit
  | succ i => simp [At] at hi

theorem pair_sequence_fails :
    ¬ Paper.Extension.Eqv (Φ := Empty) Paper.UnaryReturn.Step [source]
      (returnOnce (.pair (.let₁ (.var 0) (.var 0)) (.var 0)))
      (pairSequence (.let₁ (.var 0) (.var 0)) (.var 0)) [product source source] := by
  intro h
  have obs := extended_same (observation := { pairLet := true }) rfl h env env_typed
  change Result.fault = .jump 0 (.pair (.inl .unit) (.inl .unit)) at obs
  cases obs

theorem fusion_cannot_sequence_constructors :
    ¬ ConstructorSequencing (τ := Ty Empty) (Φ := Empty) Paper.UnaryReturn.Step := by
  intro seq
  have leftNorm : Normalizes [source] (.let₁ (.var 0) (.var 0) : Tm Empty) (.var 0) source :=
    .let₁ (.value (.var (i := 0) rfl)) (.value (.var (i := 0) rfl))
  have rightNorm : Normalizes [source] (.var 0 : Tm Empty) (.var 0) source :=
    .value (.var (i := 0) rfl)
  exact pair_sequence_fails (seq.pair leftNorm rightNorm)

theorem mixed_state_fails :
    ¬ Paper.Extension.Eqv Paper.UnaryReturn.Step [source] (returnOnce update) (.br 0 constructor) [target] := by
  intro h
  have obs := extended_same (observation := { pairLet := true }) rfl h env env_typed
  change Result.fault = .jump 0 (.inl (.pair (.inl .unit) (.inl .unit))) at obs
  cases obs

end

open CfgEta.TypeCategory (returnRegion)

universe u v

variable {α : Type u} {Φ : Type v} [HasTy Φ (Ty α)]

-- The projection laws respect both typed unit observations.
set_option linter.concreteInstances false in
private theorem projection_same [Observer.UnitPayloadPolicy] {observation : Observer.TermObservation (α := α) Φ} {Γ L : List (Ty α)} {r s : Region Φ}
    (h : Paper.WithProjectionReturns.Step Γ r s L) : Observer.SameWith observation Γ r s := by
  cases h <;> intro env _ <;> cases hx : env 0 <;>
    simp [returnRegion, Observer.evalRegionWith, Observer.evalTermWith, Observer.startsLet, Observer.computes, hx, extend]

open scoped Observer.AlternateUnit in
theorem projection_unit_eta_fails :
    ¬ Paper.Extension.Eqv Paper.WithProjectionReturns.Step [(Ty.unit : Ty Empty)]
      (.br 0 (.unit : Tm Empty)) (.br 0 (.var 0)) [Ty.unit] := by
  intro h
  let env : Env := fun _ => .inl .unit
  have henv : EnvTy [(Ty.unit : Ty Empty)] env := by
    intro i A hi
    cases i with
    | zero => cases Option.some.inj hi; exact .alternateUnit rfl
    | succ i => simp [At] at hi
  have obs := Observer.extension_same (observation := { pairLet := true }) projection_same h env henv
  change Result.jump 0 .unit = Result.jump 0 (.inl .unit) at obs
  cases obs

section
open scoped Observer.CanonicalUnit

private theorem unit_same {observation : Observer.TermObservation (α := α) Φ} {Γ L : List (Ty α)} {r s : Region Φ}
    (h : Paper.WithUnitEta.Step Γ r s L) : Observer.SameWith observation Γ r s := by
  cases h
  intro env he
  have ht := he (rfl : At [Ty.unit] 0 (Ty.unit : Ty α))
  have hu : env 0 = .unit := ht.eq_unit rfl
  simp [Observer.evalRegionWith, Observer.evalTermWith, hu]

theorem projectionUnitSeed_same {observation : Observer.TermObservation (α := α) Φ}
    {Γ L : List (Ty α)} {r s : Region Φ}
    (h : Paper.WithProjectionReturnsAndUnitEta.Step Γ r s L) : Observer.SameWith observation Γ r s :=
  h.elim projection_same unit_same

theorem joined_same {observation : Observer.TermObservation (α := α) Φ} {Γ L : List (Ty α)} {r s : Region Φ}
    (h : Paper.Extension.Eqv Paper.WithProjectionReturnsAndUnitEta.Step Γ r s L) : Observer.SameWith observation Γ r s :=
  Observer.extension_same projectionUnitSeed_same h

/-- The witness uses variable and unary-let expressions inside a pair. Both
the projection-return and unit seeds preserve its separating observation. -/
theorem lowered_pure_pair_discard_fails :
    ¬ Paper.Extension.Eqv
      (fun Γ r s L => Paper.WithProjectionReturns.Step Γ r s L ∨ Paper.WithUnitEta.Step Γ r s L)
      [source]
      (compLSubst (fun _ => returnRegion (.pair (.let₁ (.var 0) (.var 0)) (.var 0) : Tm Empty))
        (fun _ => .br 0 .unit) 0)
      (.br 0 .unit) [Ty.unit] := by
  intro h
  have same := joined_same (observation := { pairLet := true }) h
  have obs := same env env_typed
  change Result.fault = .jump 0 .unit at obs
  cases obs

end

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing
