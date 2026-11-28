module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.Iteration.RequestBlocks.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RequestBlocks

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region.Paper
open CategoryTheory CategoryTheory.Limits
open Extension.Singleton
open WithPairReturns (requestBlocks)

universe u v w

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Seed" => WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe

variable {S R B : Extension.Singleton.TypeCategory (WithPairReturns.JoinedStep (τ := τ) (Φ := Φ) pe)}

local notation "I" => iterateChosen Seed

/-- The inner cut used by the source expansion repeats only into the pending block. -/
private noncomputable def innerCut (first : S ⟶ R) (second : R ⟶ B ⨿ S) :
    S ⨿ R ⟶ (B ⨿ (S ⨿ R)) ⨿ (S ⨿ R) :=
  requestBlocks pe first second ≫ coprod.map
    (coprod.map (𝟙 B) (coprod.inl : S ⟶ S ⨿ R)) (coprod.inr : R ⟶ S ⨿ R)

/-- The inner iteration factors through the original return-or-repeat sum.
Rolling then replays the square for the original-state injection. -/
private theorem iterate_innerCut (first : S ⟶ R) (second : R ⟶ B ⨿ S) :
    I (first ≫ second) = coprod.inl ≫ I (I (innerCut pe first second)) := by
  let left : S ⟶ S ⨿ R := coprod.inl
  let pending : R ⟶ S ⨿ R := coprod.inr
  let embed := coprod.map (𝟙 B) left
  let cut := innerCut pe first second
  let step := requestBlocks pe first second ≫ coprod.desc (𝟙 (B ⨿ S)) second
  have pendingExit : pending ≫ I cut = second ≫ embed := by
    conv_lhs => rw [iterateChosen_fixpoint Seed cut]
    simp [pending, cut, innerCut, requestBlocks, embed, left, Category.assoc]
  have factor : I cut = step ≫ embed := by
    conv_lhs => rw [iterateChosen_fixpoint Seed cut]
    change (requestBlocks pe first second ≫ coprod.map embed pending) ≫
      coprod.desc (𝟙 (B ⨿ (S ⨿ R))) (I cut) = _
    dsimp only [step]
    rw [Category.assoc, coprod.map_desc, Category.comp_id, pendingExit,
      Category.assoc, coprod.desc_comp, Category.id_comp]
  have fused : first ≫ second = left ≫ step := by
    simp [left, step, requestBlocks, Category.assoc]
  exact uniformity_of_factorization Seed left (first ≫ second) (I cut) step fused factor

/-- The outer cut becomes precisely the reassociated one-request table. -/
private theorem codiagonal_readback (first : S ⟶ R) (second : R ⟶ B ⨿ S) :
    I (I (innerCut pe first second)) =
      I (requestBlocks pe first second ≫ (coprod.associator B S R).hom) := by
  rw [iterateChosen_codiagonal]
  unfold innerCut
  rw [Category.assoc]
  apply congrArg (fun k => I (requestBlocks pe first second ≫ k))
  apply coprod.hom_ext
  · apply coprod.hom_ext <;> simp [coprod.associator]
  · simp [coprod.associator]

/-- Eliminate the pending-reply block using the checked inclusion square
and codiagonal readback. -/
theorem iterateChosen_requestBlocks (first : S ⟶ R) (second : R ⟶ B ⨿ S) :
    iterateChosen Seed (first ≫ second) =
      coprod.inl ≫ iterateChosen Seed (requestBlocks pe first second ≫ (coprod.associator B S R).hom) :=
  (iterate_innerCut pe first second).trans
    (congrArg (fun f => coprod.inl ≫ f) (codiagonal_readback pe first second))

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.RequestBlocks
