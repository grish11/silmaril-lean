module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Unit.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Blocks.Constructor.Thms

/-! # A three-phase loop with the two retained tags as separate blocks -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling

open CategoryTheory CategoryTheory.Limits
open UnitThreeCycle (One Three reset)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "P" => TypeCategory (τ := τ) Φ

noncomputable abbrev BitState : P := One ⨿ One
noncomputable abbrev Phases (A : P) : P := A ⨿ (A ⨿ A)

/-- Reset each Unit payload. The retained tag is preserved. -/
noncomputable abbrev resetPayloads : BitState (τ := τ) (Φ := Φ) ⟶ BitState :=
  coprod.map reset reset

/-- Change only the Unit payloads at the step boundary. The exit object
and both recursive tags are unchanged. -/
noncomputable def normalize {B : P} (g : BitState (τ := τ) (Φ := Φ) ⟶ B ⨿ BitState) :
    BitState ⟶ B ⨿ BitState :=
  resetPayloads ≫ g ≫ coprod.map (𝟙 B) resetPayloads

/-- Run the next row on a recursive result and short-circuit an exit. -/
noncomputable abbrev thenOnRepeat {A B : P} (f g : A ⟶ B ⨿ A) : A ⟶ B ⨿ A :=
  f ≫ coprod.desc coprod.inl g

/-- Express a round in isomorphic state coordinates while keeping its outward object. -/
noncomputable def transport {A D B : P} (e : A ≅ D) (g : D ⟶ B ⨿ D) : A ⟶ B ⨿ A :=
  e.hom ≫ g ≫ coprod.map (𝟙 B) e.inv

/-- Run the same round in each of the three phases and advance on recurrence. -/
noncomputable def cycle {A B : P} (g : A ⟶ B ⨿ A) : Phases A ⟶ B ⨿ Phases A :=
  coprod.desc (g ≫ coprod.map (𝟙 B) (coprod.inl ≫ coprod.inr))
    (coprod.desc (g ≫ coprod.map (𝟙 B) (coprod.inr ≫ coprod.inr))
      (g ≫ coprod.map (𝟙 B) coprod.inl))

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.ComponentTripling
