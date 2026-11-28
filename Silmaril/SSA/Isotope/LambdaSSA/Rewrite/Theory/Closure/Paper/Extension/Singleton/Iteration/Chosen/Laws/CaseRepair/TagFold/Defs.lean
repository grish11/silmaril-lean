module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.CaseRepair.Defs
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Restoration for a finite coproduct of copies of one state type -/

@[expose] public section

universe u v
set_option autoImplicit false

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.CaseRepair.TagFold

open CategoryTheory CategoryTheory.Limits

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

/-- Forget the tag and pass the retained state through unchanged. -/
noncomputable def fold {n : Nat} {D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) : tags.pt ⟶ D :=
  Cofan.IsColimit.desc ht (fun _ => 𝟙 D)

/-- Preserve the outward result and put each recursive result back in its input copy. -/
noncomputable def restore {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (p : tags.pt ⟶ B ⨿ D) : tags.pt ⟶ B ⨿ tags.pt :=
  Cofan.IsColimit.desc ht (fun i => tags.inj i ≫ p ≫ coprod.map (𝟙 B) (tags.inj i))

/-- Every arm factors through a step on its retained state with recurrence tagged by
the arm's own injection. The steps may be different and may update the retained state. -/
def PreservesTag {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (f : tags.pt ⟶ B ⨿ tags.pt) : Prop :=
  ∀ i : Fin n, ∃ step : D ⟶ B ⨿ D, tags.inj i ≫ f = step ≫ coprod.map (𝟙 B) (tags.inj i)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.CaseRepair.TagFold
