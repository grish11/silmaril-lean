module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ChosenBlockFeedback

/-! # Elimination of a recursive summand in the guarded quotient -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton

open CategoryTheory CategoryTheory.Limits
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "I" => iterateChosen Seed

/-- The restriction of a step whose feedback always enters one summand is computed by rolling. -/
theorem iterateChosen_restrict {X D B : Q} (i : D ⟶ X) (a : X ⟶ B ⨿ D) :
    i ≫ I (a ≫ coprod.map (𝟙 B) i) = I (i ≫ a) :=
  ChosenBlockFeedback.iterate_restrict Seed i a

/-- Solve the right recursive summand first, treating transfers to the left as exits.
Then iterate the resulting left step and connect its result to the right summand. -/
theorem iterateChosen_rows {A D B : Q} (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) :
    let right := I (coprod.inr ≫ d)
    let left := I ((coprod.inl ≫ d) ≫ coprod.desc (𝟙 (B ⨿ A)) right)
    I (d ≫ (coprod.associator B A D).hom) = coprod.desc left (right ≫ coprod.desc (𝟙 B) left) :=
  ChosenBlockFeedback.iterate_rows Seed d

/-- Reassociating a block step preserves and reflects its square. -/
theorem iterateChosen_block_square_iff {A D E B : Q} (h : D ⟶ E)
    (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) (e : A ⨿ E ⟶ (B ⨿ A) ⨿ E) :
    (d ≫ (coprod.associator B A D).hom) ≫ coprod.map (𝟙 B) (coprod.map (𝟙 A) h) =
        coprod.map (𝟙 A) h ≫ e ≫ (coprod.associator B A E).hom ↔
      d ≫ coprod.map (𝟙 (B ⨿ A)) h = coprod.map (𝟙 A) h ≫ e :=
  ChosenBlockFeedback.block_square_iff Seed h d e

/-- Uniformity of the right recursive block lifts to the joined step. -/
theorem iterateChosen_of_right_block {A D E B : Q} (h : D ⟶ E)
    (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) (e : A ⨿ E ⟶ (B ⨿ A) ⨿ E)
    (square : d ≫ coprod.map (𝟙 (B ⨿ A)) h = coprod.map (𝟙 A) h ≫ e)
    (inner : I (coprod.inr ≫ d) = h ≫ I (coprod.inr ≫ e)) :
    I (d ≫ (coprod.associator B A D).hom) =
      coprod.map (𝟙 A) h ≫ I (e ≫ (coprod.associator B A E).hom) :=
  ChosenBlockFeedback.iterate_of_right_block Seed h d e square inner

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton
