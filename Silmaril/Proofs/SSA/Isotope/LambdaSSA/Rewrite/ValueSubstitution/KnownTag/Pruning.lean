module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Coherence.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution.KnownTag.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.ValueSubstitution
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

/-! # Transport exact region witnesses through repeated constructor tests -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.KnownTag

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel extend_map)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
  (case_inl case_inr regionDenotes_substValue_proof)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {κ : Type u} (M : TypeModel (Ty κ) V) {Φ : Type v} [HasTy Φ (Ty κ)] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem prune_denotes {r s : Region Φ} (steps : Region.PruneConstructorTests r s)
    {Γ : VCtx (Ty κ)} {L : LCtx (Ty κ)} {h : r.HasType Γ L}
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M L)} (d : RegionDenotes J M h f) :
    ∃ hs : s.HasType Γ L, RegionDenotes J M hs f := by
  induction steps generalizing Γ L with
  | keep => exact ⟨_, d⟩
  | let₁ _ ih =>
      cases d with
      | let₁ init body =>
          obtain ⟨_, body'⟩ := ih body
          exact ⟨_, .let₁ init body'⟩
  | case _ _ ihl ihr =>
      cases d with
      | case test left right =>
          obtain ⟨_, left'⟩ := ihl left
          obtain ⟨_, right'⟩ := ihr right
          exact ⟨_, .case test left' right'⟩
  | inl _ ih =>
      cases d with
      | case test left right =>
          cases test with
          | inl payload =>
              cases payload with
              | var hit =>
                  rw [Category.assoc, ← J.map_comp, Category.assoc, Iso.inv_hom_id,
                    Category.comp_id, case_inl]
                  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map]
                  obtain ⟨_, selected⟩ :=
                    regionDenotes_substValue_proof J M left (.var hit)
                  exact ih selected
  | inr _ ih =>
      cases d with
      | case test left right =>
          cases test with
          | inr payload =>
              cases payload with
              | var hit =>
                  rw [Category.assoc, ← J.map_comp, Category.assoc, Iso.inv_hom_id,
                    Category.comp_id, case_inr]
                  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_map]
                  obtain ⟨_, selected⟩ :=
                    regionDenotes_substValue_proof J M right (.var hit)
                  exact ih selected

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.KnownTag
