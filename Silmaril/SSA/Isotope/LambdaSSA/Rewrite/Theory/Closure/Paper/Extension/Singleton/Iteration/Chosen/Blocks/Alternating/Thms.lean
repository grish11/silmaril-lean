module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.Alternating.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.AlternatingFold

/-! # Alternating fold uniformity is the two-step iteration equation -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Alternating

open CategoryTheory CategoryTheory.Limits
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "P" => Paper.TypeCategory (τ := τ) Φ
local notation "J" => projection Seed
local notation "I" => iterateChosen Seed

/-- A commuting square in the contextual quotient forces its independently
written alternating rows to agree with the target after forgetting the tag.
Block elimination then reduces uniformity exactly to doubling the target step. -/
theorem fold_iff_double {A B D : Q}
    (split : D ⨿ D ≅ A) (h : A ⟶ D) (f : A ⟶ B ⨿ A) (g left right : D ⟶ B ⨿ D)
    (hl : (coprod.inl ≫ split.hom) ≫ h = 𝟙 D)
    (hr : (coprod.inr ≫ split.hom) ≫ h = 𝟙 D)
    (routeLeft : (coprod.inl ≫ split.hom) ≫ f = left ≫ coprod.map (𝟙 B) (coprod.inr ≫ split.hom))
    (routeRight : (coprod.inr ≫ split.hom) ≫ f = right ≫ coprod.map (𝟙 B) (coprod.inl ≫ split.hom))
    (square : f ≫ coprod.map (𝟙 B) h = h ≫ g) :
    I f = h ≫ I g ↔ I (g ≫ coprod.desc coprod.inl g) = I g :=
  AlternatingFold.fold_iff_double Seed split h f g left right hl hr routeLeft routeRight square

/-- Projection preserves the two-step computation, including an exit after the first step. -/
theorem projectStep_double {D B : P} (g : D ⟶ B ⨿ D) :
    projectStep Seed (g ≫ coprod.desc coprod.inl g) =
      projectStep Seed g ≫ coprod.desc coprod.inl (projectStep Seed g) :=
  AlternatingFold.projectStep_double Seed g

/-- A standard Paper proof of the two-step iteration equation survives the contextual quotient. -/
theorem double_of_native {D B : P} (g : D ⟶ B ⨿ D)
    (native : Paper.TypeCategory.iterate (g ≫ coprod.desc coprod.inl g) = Paper.TypeCategory.iterate g) :
    I (projectStep Seed g ≫ coprod.desc coprod.inl (projectStep Seed g)) = I (projectStep Seed g) := by
  rw [← projectStep_double Seed, iterateChosen_projectStep Seed, iterateChosen_projectStep Seed, native]

/-- Replay a corrected alternating square using a native doubling proof for
its written target. The two source rows can be arbitrary quotient arrows. -/
theorem uniformity_of_native_double {A : Q} {B D : P}
    (split : (J).obj D ⨿ (J).obj D ≅ A) (h : A ⟶ (J).obj D)
    (f : A ⟶ (J).obj B ⨿ A) (g : D ⟶ B ⨿ D)
    (left right : (J).obj D ⟶ (J).obj B ⨿ (J).obj D)
    (hl : (coprod.inl ≫ split.hom) ≫ h = 𝟙 ((J).obj D))
    (hr : (coprod.inr ≫ split.hom) ≫ h = 𝟙 ((J).obj D))
    (routeLeft : (coprod.inl ≫ split.hom) ≫ f =
      left ≫ coprod.map (𝟙 ((J).obj B)) (coprod.inr ≫ split.hom))
    (routeRight : (coprod.inr ≫ split.hom) ≫ f =
      right ≫ coprod.map (𝟙 ((J).obj B)) (coprod.inl ≫ split.hom))
    (square : f ≫ coprod.map (𝟙 ((J).obj B)) h = h ≫ projectStep Seed g)
    (native : Paper.TypeCategory.iterate (g ≫ coprod.desc coprod.inl g) = Paper.TypeCategory.iterate g) :
    I f = h ≫ I (projectStep Seed g) :=
  (fold_iff_double Seed split h f (projectStep Seed g) left right hl hr routeLeft routeRight square).2
    (double_of_native Seed g native)

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.Alternating
