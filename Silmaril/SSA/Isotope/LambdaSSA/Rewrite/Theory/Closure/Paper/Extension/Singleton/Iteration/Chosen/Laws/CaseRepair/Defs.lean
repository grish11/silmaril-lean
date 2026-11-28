module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Defs

/-! # Recovering a source step with tag-dependent recurrence -/

@[expose] public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.CaseRepair

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

/-- Run the observed step, restoring its recursive payload with the map
for the current source arm. Outward payloads pass through the identity. -/
noncomputable def restore {X Y A B D : Comp} (split : X ⨿ Y ≅ A)
    (left right : D ⟶ A) (p : A ⟶ B ⨿ D) : A ⟶ B ⨿ A :=
  split.inv ≫ coprod.desc
    (coprod.inl ≫ split.hom ≫ p ≫ coprod.map (𝟙 B) left)
    (coprod.inr ≫ split.hom ≫ p ≫ coprod.map (𝟙 B) right)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.CaseRepair
