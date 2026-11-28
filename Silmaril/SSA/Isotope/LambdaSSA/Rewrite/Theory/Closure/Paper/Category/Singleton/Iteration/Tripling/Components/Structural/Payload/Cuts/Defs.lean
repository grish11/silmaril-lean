module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Tripling.Components.Structural.Payload.Defs

/-! # Left recurrence after eliminating the right tag -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle.Payload

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "Phases" A:max => (A ⨿ (A ⨿ A))
local notation "I" => iterateChosen Seed

/-- Feed the grouped right iterate back to the left row with the phase intact. -/
noncomputable def leftCut {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) : Phases A ⟶ B ⨿ Phases A :=
  (coprod.inl ≫ groupedRows Seed g) ≫ coprod.desc (𝟙 (B ⨿ Phases A)) (I (groupedRightRow Seed g))

/-- Eliminate the right row in the original one-round step. -/
noncomputable def targetLeftCut {A D B : Q} (g : A ⨿ D ⟶ B ⨿ (A ⨿ D)) : A ⟶ B ⨿ A :=
  (coprod.inl ≫ g ≫ (coprod.associator B A D).inv) ≫
    coprod.desc (𝟙 (B ⨿ A)) (I (targetRightRow Seed g))

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle.Payload
