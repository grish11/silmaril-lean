module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Thms

/-! # Entry-let sequencing by categorical CFG η -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CategoricalEntryLet

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (bind)
open Silmaril.DeBruijn (lift)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]
  [RegionTypingCoherent (Φ := Φ) J M]

omit [FreydCategory.CentralUnit J] in
private theorem denote_let {Γ : VCtx τ} {L : LCtx τ} {S : τ} {a : Tm Φ} {d : Region Φ}
    (ha : Tm.HasType Γ a S) (hd : HasType (S :: Γ) d L) :
    denoteRegion J M (.let₁ ha hd) = bind J (denote J M ha) (denoteRegion J M hd) :=
  (RegionDenotes.let₁ (denote_spec J M ha) (denoteRegion_spec J M hd)).eq_denote J M |>.symm

theorem denoteRegion_cfgEntryLet
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {S : τ} {a : Tm Φ} {d : Region Φ}
    {blocks : Fin n → Region Φ} (R : Fin n → τ)
    (ha : Tm.HasType Γ a S)
    (hd : HasType (S :: Γ) d (List.ofFn R ++ L))
    (hb : ∀ i, HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    denoteRegion J M (.cfg R (.let₁ ha hd) hb) =
      denoteRegion J M (.let₁ ha (.cfg R hd
        (fun i => (hb i).renameVars ((Ren.wk Γ S).lift (R i))))) := by
  let wb := fun i => (hb i).renameVars ((Ren.wk Γ S).lift (R i))
  have continuation := cfgEntryContinuations_hasType R wb
  have seq := hd.bindBranchArguments.hasType.lsubst continuation
  have together : ((Region.let₁ a d).bindBranchArguments.lsubst (cfgEntryContinuations blocks)) =
      .let₁ a (d.bindBranchArguments.lsubst (cfgEntryContinuations (fun i => (blocks i).renameVars (lift Nat.succ)))) := by
    simp only [bindBranchArguments, lsubst, lift_cfgEntryContinuations]
  have hs : HasType Γ ((Region.let₁ a d).bindBranchArguments.lsubst (cfgEntryContinuations blocks)) L :=
    together.symm ▸ HasType.let₁ ha seq
  have equal : denoteRegion J M hs = denoteRegion J M (.let₁ ha seq) := by
    generalize h : ((Region.let₁ a d).bindBranchArguments.lsubst (cfgEntryContinuations blocks)) = r at hs together
    cases together
    rfl
  calc
    _ = denoteRegion J M hs :=
      denoteRegion_cfgEta_bound_sharedTensor J M shared R (.let₁ ha hd) hb hs
    _ = denoteRegion J M (.let₁ ha seq) := equal
    _ = _ := by
      rw [denote_let J M ha seq, denote_let J M ha (.cfg R hd wb),
        denoteRegion_cfgEta_bound_sharedTensor J M shared R hd wb seq]

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CategoricalEntryLet
