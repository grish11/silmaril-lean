module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
public import Silmaril.Semantics.Categories.Freyd.Parallel.Thms

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Parallel (Derivation Pure)
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj extend_map pair_maps_eq_map_lift)
open LetIter.ProofRelevant.Semantics.Categorical (caseWithContext splitMapCoprod)

universe v₁ v₂ u₁ u₂ u v w q

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C)

private theorem case_maps [DistributiveFreydCategory J] {R A B D : V} (s : R ⟶ A ⨿ B)
    (l : R ⊗ A ⟶ D) (r : R ⊗ B ⟶ D) :
    caseWithContext J (J.map s) (J.map l) (J.map r) =
      J.map (lift (𝟙 R) s ≫ (DistributiveTensor.leftIso R A B).inv ≫ coprod.desc l r) := by
  have copair : splitMapCoprod J (R ⊗ A) (R ⊗ B) ≫ coprod.desc (J.map l) (J.map r) =
      J.map (coprod.desc l r) := by
    apply (cancel_epi (coprodComparison J (R ⊗ A) (R ⊗ B))).1
    unfold splitMapCoprod
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    apply coprod.hom_ext <;>
      simp only [coprodComparison, coprod.inl_desc_assoc, coprod.inr_desc_assoc,
        ← J.map_comp, coprod.inl_desc, coprod.inr_desc]
  simp only [caseWithContext, LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map, copair, J.map_comp]

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  [∀ X Y : C, Preorder (X ⟶ Y)] (P : FreydCategory.OrderedParallel J)
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] [InstructionModel J M Φ]
  {ε : Type q} [HasEff Φ ε] {pe : ε}

set_option backward.isDefEq.respectTransparency false in
theorem denote_pure_proof
    (pureInstr : ∀ f : Φ, IsPure pe f →
      ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
        InstructionModel.denote (J := J) (M := M) f = J.map p)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) (hp : Pure pe t) :
    ∃ p : envObj M Γ β ⟶ M.obj A, denote J P M d = J.map p := by
  induction d with
  | fv | bv | unit => exact ⟨_, rfl⟩
  | op _ ih =>
    cases hp with
    | op hf ha =>
      obtain ⟨p, dp⟩ := ih ha
      obtain ⟨q, dq⟩ := pureInstr _ hf
      exact ⟨p ≫ q, by simp only [denote, dp, dq, ← J.map_comp]⟩
  | let₁ _ _ ih₁ ih₂ | let₂ _ _ ih₁ ih₂ =>
    cases hp
    obtain ⟨_, dp⟩ := ih₁ ‹Pure pe _›
    obtain ⟨_, dq⟩ := ih₂ ‹Pure pe _›
    simp only [denote, dp, dq, LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map, ← J.map_comp]
    exact ⟨_, rfl⟩
  | pair _ _ ih₁ ih₂ | par _ _ ih₁ ih₂ =>
    cases hp
    obtain ⟨_, dp⟩ := ih₁ ‹Pure pe _›
    obtain ⟨_, dq⟩ := ih₂ ‹Pure pe _›
    simp only [denote, dp, dq, pair_maps_eq_map_lift, P.par_maps, ← J.map_comp]
    exact ⟨_, rfl⟩
  | inl _ ih | inr _ ih | abort _ ih =>
    cases hp
    obtain ⟨_, dp⟩ := ih ‹Pure pe _›
    simp only [denote, dp, ← J.map_comp]
    exact ⟨_, rfl⟩
  | case _ _ _ ih₁ ih₂ ih₃ =>
    cases hp with
    | case he hl hr =>
      obtain ⟨_, de⟩ := ih₁ he
      obtain ⟨_, dl⟩ := ih₂ hl
      obtain ⟨_, dr⟩ := ih₃ hr
      simp only [denote, de, dl, dr, ← J.map_comp, case_maps]
      exact ⟨_, rfl⟩
  | iter => cases hp

end Silmaril.Isotope.LetParIter.Categorical
