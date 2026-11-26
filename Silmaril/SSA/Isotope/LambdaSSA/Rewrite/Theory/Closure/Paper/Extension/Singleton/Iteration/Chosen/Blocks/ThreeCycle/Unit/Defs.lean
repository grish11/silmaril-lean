module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Values.CartesianBoundary.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Thms

/-! # The native three-cycle with Unit payloads -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.UnitThreeCycle

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ

abbrev unitTy : τ := Silmaril.unit
abbrev twoTy : τ := Silmaril.coprod unitTy unitTy
abbrev threeTy : τ := Silmaril.coprod unitTy twoTy
abbrev One : P := ofType unitTy
abbrev Three : P := ofType threeTy

/-- Compare the written three-way state type with three copies of Unit. -/
noncomputable def split : Three (τ := τ) (Φ := Φ) ≅ One ⨿ (One ⨿ One) :=
  sumIso unitTy twoTy ≪≫ coprod.mapIso (Iso.refl _) (sumIso unitTy unitTy)

abbrev reset : One (τ := τ) (Φ := Φ) ⟶ One := discardArrow unitTy
abbrev forget : Three (τ := τ) (Φ := Φ) ⟶ One := discardArrow threeTy

/-- The written cycle executes the same round in all phases. On recurrence
it advances one phase, and on exit it forwards the result. -/
noncomputable def step {B : P} (g : One ⟶ B ⨿ One) : Three ⟶ B ⨿ Three :=
  let e := split (τ := τ) (Φ := Φ)
  e.hom ≫ coprod.desc
    (g ≫ coprod.map (𝟙 B) (coprod.inl ≫ coprod.inr ≫ e.inv))
    (coprod.desc (g ≫ coprod.map (𝟙 B) (coprod.inr ≫ coprod.inr ≫ e.inv))
      (g ≫ coprod.map (𝟙 B) (coprod.inl ≫ e.inv)))

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.UnitThreeCycle
