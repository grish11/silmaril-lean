module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Defs

/-! # Feedback between two alternating copies of a retained state -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Alternating

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

local notation "Q" => TypeCategory Seed

/-- Each row can exit or update its retained state and recur into the other copy. -/
noncomputable abbrev step {D B : Q} (left right : D ⟶ B ⨿ D) : D ⨿ D ⟶ B ⨿ (D ⨿ D) :=
  coprod.desc (left ≫ coprod.map (𝟙 B) coprod.inr) (right ≫ coprod.map (𝟙 B) coprod.inl)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Alternating
