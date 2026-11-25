module

public import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.TheoryTyping
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators

/-! # Categorical evaluation of branch substitution -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

section Values

variable (J : Functor V C) [DistributiveFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

private theorem branchValue_subst_denotes {Γ Δ : VCtx τ} {b : Tm Φ} {B : τ}
    (hb : Tm.BranchValue Δ b B) (σ : Nat → Tm Φ) (k : ctxObj M Γ ⟶ ctxObj M Δ)
    (hσ : ∀ ⦃i A⦄, (hi : At Δ i A) → ∃ h : Tm.HasType Γ (σ i) A,
      Denotes J M h (J.map (k ≫ lookup M i hi))) :
    ∃ (ht : Tm.HasType Γ (b.subst σ) B) (g : ctxObj M Δ ⟶ M.obj B),
      Denotes J M hb.hasType (J.map g) ∧ Denotes J M ht (J.map (k ≫ g)) := by
  induction hb with
  | var hi =>
      obtain ⟨h, dh⟩ := hσ hi
      exact ⟨h, _, .var hi, dh⟩
  | unit =>
      refine ⟨.unit, _, .unit, ?_⟩
      have h : k ≫ CartesianMonoidalCategory.toUnit _ = CartesianMonoidalCategory.toUnit _ :=
        (CartesianMonoidalCategory.isTerminalTensorUnit).hom_ext _ _
      rw [← Category.assoc, h]
      exact .unit
  | pair _ _ ihl ihr =>
      obtain ⟨hl, f, df, df'⟩ := ihl
      obtain ⟨hr, g, dg, dg'⟩ := ihr
      refine ⟨.pair hl hr, CartesianMonoidalCategory.lift f g ≫ (M.productIso _ _).inv, ?_, ?_⟩
      · rw [J.map_comp, ← pair_map]
        exact .pair df dg
      · rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, J.map_comp, ← pair_map]
        exact .pair df' dg'
  | inl _ ih =>
      obtain ⟨h, g, dg, dg'⟩ := ih
      refine ⟨.inl h, g ≫ coprod.inl ≫ (M.coprodIso _ _).inv, ?_, ?_⟩
      · rw [J.map_comp]
        exact .inl dg
      · rw [← Category.assoc, J.map_comp]
        exact .inl dg'
  | inr _ ih =>
      obtain ⟨h, g, dg, dg'⟩ := ih
      refine ⟨.inr h, g ≫ coprod.inr ≫ (M.coprodIso _ _).inv, ?_, ?_⟩
      · rw [J.map_comp]
        exact .inr dg
      · rw [← Category.assoc, J.map_comp]
        exact .inr dg'

end Values

section Regions

variable [Iteration C] [ElgotCategory C] (J : Functor V C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem letBr_common {Γ : VCtx τ} {L : LCtx τ} {a b : Tm Φ} {A B : τ} {ℓ : Nat}
    (ha : Tm.BranchValue Γ a A) (hb : Tm.BranchValue (A :: Γ) b B) (hℓ : At L ℓ B) :
    ∃ (hs : Region.HasType Γ (.let₁ a (.br ℓ b)) L)
      (ht : Region.HasType Γ (.br ℓ (b.subst (Tm.singleSubst a))) L),
      ∃ f, RegionDenotes J M hs f ∧ RegionDenotes J M ht f := by
  obtain ⟨p, dp⟩ := ha.denotes_map J M
  let k : ctxObj M Γ ⟶ ctxObj M (A :: Γ) := CartesianMonoidalCategory.lift (𝟙 _) p
  have hσ : ∀ ⦃i D⦄, (hi : At (A :: Γ) i D) → ∃ h : Tm.HasType Γ (Tm.singleSubst a i) D,
      Denotes J M h (J.map (k ≫ lookup M i hi)) := by
    intro i D hi
    cases i with
    | zero =>
        have h : A = D := Option.some.inj hi
        cases h
        change ∃ h : Tm.HasType Γ a A, Denotes J M h
          (J.map (k ≫ CartesianMonoidalCategory.snd (ctxObj M Γ) (M.obj A)))
        have hp : k ≫ CartesianMonoidalCategory.snd (ctxObj M Γ) (M.obj A) = p :=
          CartesianMonoidalCategory.lift_snd _ _
        rw [hp]
        exact ⟨ha.hasType, dp⟩
    | succ i =>
        have h : At Γ i D := hi
        change ∃ h' : Tm.HasType Γ (.var i) D, Denotes J M h'
          (J.map (k ≫ CartesianMonoidalCategory.fst (ctxObj M Γ) (M.obj A) ≫ lookup M i h))
        have hp : k ≫ CartesianMonoidalCategory.fst (ctxObj M Γ) (M.obj A) = 𝟙 _ :=
          CartesianMonoidalCategory.lift_fst _ _
        rw [← Category.assoc, hp, Category.id_comp]
        exact ⟨.var h, .var h⟩
  obtain ⟨ht, g, dg, dg'⟩ := branchValue_subst_denotes J M hb (Tm.singleSubst a) k hσ
  have dlet := RegionDenotes.let₁ dp (.br (h := hℓ) dg)
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    extend_map] at dlet
  have dr := RegionDenotes.br (h := hℓ) dg'
  rw [Functor.map_comp, Category.assoc] at dr
  exact ⟨_, .br hℓ ht, _, dlet, dr⟩

end Regions

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
