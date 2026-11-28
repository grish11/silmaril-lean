module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithAdministrativeReturns.WithGuardedTablePacking.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Phases.Defs

/-! # An opt-in quotient with uniformity along phase folds

One family of equations is added to `WithGuardedTablePacking`. Default
Paper and `WithGuardedTablePacking` are unchanged.
-/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity

open CategoryTheory CategoryTheory.Limits
open Paper.TypeCategory (ofType ofRegion iterate phaseType phaseFold)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

/-- Uniformity of guarded feedback along the map forgetting the phase.

Take `k + 1` phases of a state `A`, a step `f` on the phases and a step
`g` on the state, both arrows of default Paper, such that the fold is a
simulation: `f ≫ (id + fold) = fold ≫ g` holds in default Paper. Then a
guarded region representing the loop of `f` is related to a guarded region
representing the fold followed by the loop of `g`.

The state map is fixed to the fold. The square is required in default
Paper, not in any extension. -/
inductive PhaseUniform : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop
  | fold (k : Nat) {A B : τ}
      (f : ofType (Φ := Φ) (phaseType A k) ⟶ ofType B ⨿ ofType (phaseType A k))
      (g : ofType (Φ := Φ) A ⟶ ofType B ⨿ ofType A)
      (square : f ≫ coprod.map (𝟙 _) (phaseFold A k) = phaseFold A k ≫ g)
      {r s : Region Φ} (hr : ValueBranches [phaseType A k] r [B])
      (hs : ValueBranches [phaseType A k] s [B])
      (left : ofRegion hr = iterate f) (right : ofRegion hs = phaseFold A k ≫ iterate g) :
      PhaseUniform [phaseType A k] r s [B]

/-- Keep every seed of the table-packing quotient and adjoin phase uniformity. -/
abbrev Step (Γ : VCtx τ) (r s : Region Φ) (L : LCtx τ) : Prop :=
  WithGuardedTablePacking.Step pe Γ r s L ∨ PhaseUniform Γ r s L

abbrev Eqv := Paper.Extension.Eqv (Step (τ := τ) (Φ := Φ) pe)
abbrev TypeCategory := Paper.Extension.Singleton.TypeCategory (Step (τ := τ) (Φ := Φ) pe)

abbrev projection : Paper.TypeCategory (τ := τ) Φ ⥤ TypeCategory (τ := τ) (Φ := Φ) pe :=
  Paper.Extension.Singleton.projection (Step pe)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithAdministrativeReturns.WithGuardedTablePacking.WithPhaseUniformity
