module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.Thms

/-! # Feedback through three copies of a state -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle

open CategoryTheory CategoryTheory.Limits

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}

local notation "Q" => TypeCategory Seed

/-- Forget which of the three copies supplied the state. -/
noncomputable abbrev fold (A : Q) : A ⨿ (A ⨿ A) ⟶ A :=
  coprod.desc (𝟙 A) (coprod.desc (𝟙 A) (𝟙 A))

/-- Execute one round, sending recursive outputs to the next copy. -/
noncomputable def step {A B : Q} (g : A ⟶ B ⨿ A) : A ⨿ (A ⨿ A) ⟶ B ⨿ (A ⨿ (A ⨿ A)) :=
  coprod.desc (g ≫ coprod.map (𝟙 B) (coprod.inl ≫ coprod.inr))
    (coprod.desc (g ≫ coprod.map (𝟙 B) (coprod.inr ≫ coprod.inr))
      (g ≫ coprod.map (𝟙 B) coprod.inl))

/-- Execute the indicated round at each phase and advance on recurrence.
Each phase shares the same outward object. -/
noncomputable def cycleRows {A B : Q} (first middle last : A ⟶ B ⨿ A) :
    A ⨿ (A ⨿ A) ⟶ B ⨿ (A ⨿ (A ⨿ A)) :=
  coprod.desc (first ≫ coprod.map (𝟙 B) (coprod.inl ≫ coprod.inr))
    (coprod.desc (middle ≫ coprod.map (𝟙 B) (coprod.inr ≫ coprod.inr))
      (last ≫ coprod.map (𝟙 B) coprod.inl))

/-- Batch the three designated rounds, returning as soon as one exits. -/
noncomputable abbrev batchRows {A B : Q} (first middle last : A ⟶ B ⨿ A) : A ⟶ B ⨿ A :=
  first ≫ coprod.desc coprod.inl (middle ≫ coprod.desc coprod.inl last)

/-- Run up to three rounds, stopping as soon as any round exits. -/
noncomputable abbrev triple {A B : Q} (g : A ⟶ B ⨿ A) : A ⟶ B ⨿ A :=
  g ≫ coprod.desc coprod.inl (g ≫ coprod.desc coprod.inl g)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.ThreeCycle
