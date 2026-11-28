module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Unit.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycleRecurrence

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory Seed
local notation "I" => iterateChosen Seed

private theorem iterate_through {A D B : Q} (first : A ⟶ B ⨿ D) (restore : D ⟶ A) :
    I (first ≫ coprod.map (𝟙 B) restore) =
      first ≫ coprod.desc (𝟙 B) (I (restore ≫ first)) := by
  let g := first ≫ coprod.map (𝟙 B) restore
  have inner : I (restore ≫ first) = restore ≫ I g :=
    uniformity_of_factorization Seed restore (restore ≫ first) g first rfl rfl
  calc
    I g = g ≫ coprod.desc (𝟙 B) (I g) := iterateChosen_fixpoint Seed g
    _ = first ≫ coprod.desc (𝟙 B) (I (restore ≫ first)) := by
      simp only [g, Category.assoc, coprod.map_desc, Category.id_comp, inner]

theorem triple_step_through {A D B : Q} (first : A ⟶ B ⨿ D) (restore : D ⟶ A)
    (small : I (ThreeCycle.triple (restore ≫ first)) = I (restore ≫ first)) :
    let g := first ≫ coprod.map (𝟙 B) restore
    I (ThreeCycle.triple g) = I g := by
  let map := coprod.map (𝟙 B) restore
  let g := first ≫ map
  let q := restore ≫ first
  let extra := first ≫ coprod.desc coprod.inl (q ≫ coprod.desc coprod.inl q)
  have push (h : A ⟶ B ⨿ A) :
      g ≫ coprod.desc coprod.inl h = first ≫ coprod.desc coprod.inl (restore ≫ h) := by
    simp only [g, map, Category.assoc, coprod.map_desc, Category.id_comp]
  have pack (h : D ⟶ B ⨿ D) :
      coprod.desc coprod.inl (h ≫ map) = coprod.desc coprod.inl h ≫ map := by
    simp only [map, coprod.desc_comp, coprod.inl_map, Category.id_comp]
  have two : g ≫ coprod.desc coprod.inl g = (first ≫ coprod.desc coprod.inl q) ≫ map := by
    rw [push, show restore ≫ g = q ≫ map from (Category.assoc _ _ _).symm, pack, Category.assoc]
  have three : ThreeCycle.triple g = extra ≫ map := by
    change g ≫ coprod.desc coprod.inl (g ≫ coprod.desc coprod.inl g) = _
    rw [two, push, ← Category.assoc restore (first ≫ coprod.desc coprod.inl q),
      ← Category.assoc restore first, pack, Category.assoc]
    simp only [extra, q, Category.assoc]
  have prepare : restore ≫ extra = ThreeCycle.triple q := (Category.assoc _ _ _).symm
  change I (ThreeCycle.triple g) = I g
  rw [three, iterate_through, show g = first ≫ coprod.map (𝟙 B) restore from rfl,
    iterate_through, prepare, small]
  simp only [extra, Category.assoc, coprod.desc_comp, coprod.inl_desc]
  change first ≫ coprod.desc (𝟙 B) (q ≫ coprod.desc (𝟙 B) (q ≫ coprod.desc (𝟙 B) (I q))) =
    first ≫ coprod.desc (𝟙 B) (I q)
  rw [← iterateChosen_fixpoint Seed q, ← iterateChosen_fixpoint Seed q]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.ThreeCycleRecurrence
