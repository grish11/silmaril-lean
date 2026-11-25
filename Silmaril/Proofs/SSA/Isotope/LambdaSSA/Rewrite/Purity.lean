module

public import Silmaril.Raw.SSA.Isotope.LambdaSSA.Purity
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators

/-! # Categorical interpretation of the native pure expression judgment -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext splitMapCoprod)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]

private theorem case_map {E A B D : V} (f : E ⟶ A ⨿ B) (l : E ⊗ A ⟶ D) (r : E ⊗ B ⟶ D) :
    caseWithContext J (J.map f) (J.map l) (J.map r) =
      J.map (CartesianMonoidalCategory.lift (𝟙 E) f ≫
        (DistributiveTensor.leftIso E A B).inv ≫ coprod.desc l r) := by
  have hd : splitMapCoprod J (E ⊗ A) (E ⊗ B) ≫ coprod.desc (J.map l) (J.map r) =
      J.map (coprod.desc l r) := by
    let X := E ⊗ A
    let Y := E ⊗ B
    apply (cancel_epi (coprodComparison J X Y)).1
    unfold splitMapCoprod
    rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
    apply coprod.hom_ext
    · simp only [coprodComparison, coprod.inl_desc_assoc, ← J.map_comp, coprod.inl_desc]
    · simp only [coprodComparison, coprod.inr_desc_assoc, ← J.map_comp, coprod.inr_desc]
  simp only [caseWithContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    extend_map, hd, J.map_comp]

variable {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  {ε : Type u₅} [HasEff Φ ε] {pureEff : ε}

set_option backward.isDefEq.respectTransparency false in
theorem pure_denotes_map
    (hInstr : ∀ f : Φ, IsPure pureEff f →
      ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f), InstructionModel.denote (J := J) (M := M) f = J.map p)
    {Γ : VCtx τ} {a : Tm Φ} {A : τ} (ht : Tm.HasType Γ a A) (hp : Tm.Pure pureEff a) :
    ∃ p : ctxObj M Γ ⟶ M.obj A, Denotes J M ht (J.map p) := by
  induction ht with
  | var h => exact ⟨_, .var h⟩
  | unit => exact ⟨_, .unit⟩
  | @op Γ a f haTy ih =>
      cases hp with
      | op hf ha =>
          obtain ⟨p, dp⟩ := ih ha
          obtain ⟨q, hq⟩ := hInstr f hf
          have d : Denotes J M (Tm.HasType.op haTy) (J.map p ≫ InstructionModel.denote f) :=
            .op dp
          rw [hq, ← J.map_comp] at d
          exact ⟨_, d⟩
  | let₁ _ _ iha ihb =>
      cases hp with
      | let₁ ha hb =>
          obtain ⟨p, dp⟩ := iha ha
          obtain ⟨q, dq⟩ := ihb hb
          have d := Denotes.let₁ dp dq
          simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
            extend_map, ← J.map_comp] at d
          exact ⟨_, d⟩
  | let₂ _ _ iha ihb =>
      cases hp with
      | let₂ ha hb =>
          obtain ⟨p, dp⟩ := iha ha
          obtain ⟨q, dq⟩ := ihb hb
          have d := Denotes.let₂ dp dq
          simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
            extend_map, ← J.map_comp] at d
          exact ⟨_, d⟩
  | pair _ _ iha ihb =>
      cases hp with
      | pair ha hb =>
          obtain ⟨p, dp⟩ := iha ha
          obtain ⟨q, dq⟩ := ihb hb
          have d := Denotes.pair dp dq
          simp only [pair_map, ← J.map_comp] at d
          exact ⟨_, d⟩
  | @inl _ _ _ B _ ih =>
      cases hp with
      | inl ha =>
          obtain ⟨p, dp⟩ := ih ha
          have d := Denotes.inl (B := B) dp
          rw [← J.map_comp] at d
          exact ⟨_, d⟩
  | @inr _ _ A _ _ ih =>
      cases hp with
      | inr hb =>
          obtain ⟨p, dp⟩ := ih hb
          have d := Denotes.inr (A := A) dp
          rw [← J.map_comp] at d
          exact ⟨_, d⟩
  | case _ _ _ ihe ihl ihr =>
      cases hp with
      | case he hl hr =>
          obtain ⟨p, dp⟩ := ihe he
          obtain ⟨q, dq⟩ := ihl hl
          obtain ⟨s, ds⟩ := ihr hr
          have d := Denotes.case dp dq ds
          rw [← J.map_comp, case_map J] at d
          exact ⟨_, d⟩
  | @abort _ _ A _ ih =>
      cases hp with
      | abort ha =>
          obtain ⟨p, dp⟩ := ih ha
          have d := Denotes.abort (A := A) dp
          rw [← J.map_comp] at d
          exact ⟨_, d⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
