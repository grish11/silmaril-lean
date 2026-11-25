module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open CategoryTheory.CartesianMonoidalCategory (lift)
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (extend duplicate retainedContext caseWithContext splitMapCoprod)
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm Pure)

local notation "pairArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅ u₆

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)

section Distributive

variable [DistributiveFreydCategory J]

private theorem extend_map {R A : V} (f : R ⟶ A) :
    extend J (J.map f) = J.map (lift (𝟙 R) f) := by
  simp only [extend, leftTensor, id_whiskerRight, Category.id_comp,
    Functor.StrongPremonoidal.tensor_naturality_right,
    Iso.inv_hom_id_assoc, ← J.map_comp]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp [duplicate]

private theorem pair_map {R A B : V} (f : R ⟶ A) (g : R ⟶ B) :
    pairArrow J (J.map f) (J.map g) = J.map (lift f g) := by
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair,
    Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, retainedContext,
    extend_map, ← J.map_comp]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

private theorem case_map {R A B D : V} (f : R ⟶ A ⨿ B)
    (l : R ⊗ A ⟶ D) (r : R ⊗ B ⟶ D) :
    caseWithContext J (J.map f) (J.map l) (J.map r) =
      J.map (lift (𝟙 R) f ≫ (DistributiveTensor.leftIso R A B).inv ≫ coprod.desc l r) := by
  have copair : splitMapCoprod J (R ⊗ A) (R ⊗ B) ≫ coprod.desc (J.map l) (J.map r) =
      J.map (coprod.desc l r) := by
    apply (cancel_epi (coprodComparison J (R ⊗ A) (R ⊗ B))).1
    unfold splitMapCoprod
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    apply coprod.hom_ext <;>
      simp only [coprodComparison, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
        ← J.map_comp, coprod.inl_desc, coprod.inr_desc]
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    extend_map, copair, J.map_comp]

end Distributive

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₅} [HasTy Φ τ] [InstructionModel J M Φ]
  {ε : Type u₆} [HasEff Φ ε] {pureEff : ε}

theorem denote_pure_factor_proof
    (hInstr : ∀ f : Φ, IsPure pureEff f →
      ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
        InstructionModel.denote (J := J) (M := M) f = J.map p)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) (hp : Pure pureEff t) :
    ∃ p : envObj M Γ β ⟶ M.obj A, denote J M d = J.map p := by
  induction d with
  | fv | bv | unit => exact ⟨_, rfl⟩
  | @op _ _ f _ _ ih =>
      cases hp with
      | op hf ha =>
          obtain ⟨p, dp⟩ := ih ha
          obtain ⟨q, dq⟩ := hInstr f hf
          simp only [denote, dp, dq, ← J.map_comp]
          exact ⟨_, rfl⟩
  | let₁ _ _ iha ihb =>
      cases hp with
      | let₁ ha hb =>
          obtain ⟨p, dp⟩ := iha ha
          obtain ⟨q, dq⟩ := ihb hb
          simp only [denote, dp, dq, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
            extend_map, ← J.map_comp]
          exact ⟨_, rfl⟩
  | pair _ _ iha ihb =>
      cases hp with
      | pair ha hb =>
          obtain ⟨p, dp⟩ := iha ha
          obtain ⟨q, dq⟩ := ihb hb
          simp only [denote, dp, dq, pair_map, ← J.map_comp]
          exact ⟨_, rfl⟩
  | let₂ _ _ iha ihb =>
      cases hp with
      | let₂ ha hb =>
          obtain ⟨p, dp⟩ := iha ha
          obtain ⟨q, dq⟩ := ihb hb
          simp only [denote, dp, dq, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
            extend_map, ← J.map_comp]
          exact ⟨_, rfl⟩
  | inl _ ih =>
      cases hp with
      | inl ha =>
          obtain ⟨p, dp⟩ := ih ha
          simp only [denote, dp, ← J.map_comp]
          exact ⟨_, rfl⟩
  | inr _ ih =>
      cases hp with
      | inr ha =>
          obtain ⟨p, dp⟩ := ih ha
          simp only [denote, dp, ← J.map_comp]
          exact ⟨_, rfl⟩
  | case _ _ _ ihe ihl ihr =>
      cases hp with
      | case he hl hr =>
          obtain ⟨p, dp⟩ := ihe he
          obtain ⟨l, dl⟩ := ihl hl
          obtain ⟨r, dr⟩ := ihr hr
          simp only [denote, dp, dl, dr, ← J.map_comp, case_map]
          exact ⟨_, rfl⟩
  | abort _ ih =>
      cases hp with
      | abort ha =>
          obtain ⟨p, dp⟩ := ih ha
          simp only [denote, dp, ← J.map_comp]
          exact ⟨_, rfl⟩
  | iter => cases hp

end Silmaril.Isotope.LetIter.Semantics.Categorical
