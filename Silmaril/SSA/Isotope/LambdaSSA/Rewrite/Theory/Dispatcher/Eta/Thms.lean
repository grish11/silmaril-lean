module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Dispatcher.Eta.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Categorical.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Continuations.Direct.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.CfgLinkedEta

/-! # Categorical CFG η using linked continuations -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Isotope.LambdaSSA

/-- Each entry continuation receives one selected payload and runs the same
CFG with the original exact exits. -/
theorem Region.cfgEntryContinuations_hasType
    {τ : Type u₃} [TypeFormers τ] {Φ : Type u₄} [HasTy Φ τ]
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ}
    (R : Fin n → τ) {blocks : Fin n → Region Φ}
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    Region.LSubst.HasType Γ (List.ofFn R ++ L) L (Region.cfgEntryContinuations blocks) :=
  fun _ A h => .cfg R (.br h (.var rfl))
    (fun i => (hb i).renameVars ((SSA.Ren.wk Γ A).lift (R i)))

/-- Weakening a re-entry family is the re-entry family of the weakened table. -/
theorem Region.lift_cfgEntryContinuations {Φ : Type u₄} {n : Nat} (blocks : Fin n → Region Φ) :
    liftLSubstVars (cfgEntryContinuations blocks) =
      cfgEntryContinuations (fun i => (blocks i).renameVars (Silmaril.DeBruijn.lift Nat.succ)) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.lift_cfgEntryContinuations blocks

namespace Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)

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

/-- The original CFG and its linked re-entry family have a common
categorical denotation. This is CFG η with the continuation applied as a
linked CFG. The entry and each local block may themselves be nested CFGs. -/
theorem cfgLinkedEta_denotes {n : Nat} {Γ : VCtx τ} {L : LCtx τ}
    {entry : Region Φ} (R : Fin n → τ) {blocks : Fin n → Region Φ}
    (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    ∃ ht : Region.HasType Γ (entry.linkExits (List.ofFn R ++ L) (Region.cfgEntryContinuations blocks)) L,
      ∃ f, RegionDenotes J M (.cfg R he hb) f ∧ RegionDenotes J M ht f := by
  obtain ⟨ht, f, _, df, dt, _⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfg_linked_eta_common J M R he hb
  exact ⟨ht, f, df, dt⟩

/-- Categorical CFG η for the linked representation of typed continuations. -/
theorem denoteRegion_cfgLinkedEta [RegionTypingCoherent (Φ := Φ) J M]
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ}
    {entry : Region Φ} (R : Fin n → τ) {blocks : Fin n → Region Φ}
    (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    (hs : Region.HasType Γ (entry.linkExits (List.ofFn R ++ L) (Region.cfgEntryContinuations blocks)) L) :
    denoteRegion J M (.cfg R he hb) = denoteRegion J M hs := by
  obtain ⟨_, _, d, d'⟩ := cfgLinkedEta_denotes J M R he hb
  exact (RegionDenotes.eq_denote J M d).symm.trans (RegionDenotes.eq_denote (h := hs) J M d')

section SharedTensor

variable [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
    Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)

include shared

/-- Figure 20 CFG η for literal substitution into an entry with pure branch
arguments. All local blocks may contain arbitrary effects and nested CFGs. -/
theorem denoteRegion_cfgEta_sharedTensor
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ}
    {entry : Region Φ} (R : Fin n → τ) {blocks : Fin n → Region Φ}
    (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    (pureBranches : PureBranches J M Γ entry (List.ofFn R ++ L))
    (hs : Region.HasType Γ (entry.lsubst (Region.cfgEntryContinuations blocks)) L) :
    denoteRegion J M (.cfg R he hb) = denoteRegion J M hs := by
  obtain ⟨hl, _, _, d, dl, hk⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfg_linked_eta_common J M R he hb
  rw [denoteRegion_lsubst_sharedTensor J M shared he hs pureBranches hk, ← denoteRegion_linkExits J M he hl hk]
  exact (RegionDenotes.eq_denote J M d).symm.trans (RegionDenotes.eq_denote J M dl)

/-- CFG η for any exactly typed entry, evaluating each outward payload once
before literal substitution. -/
theorem denoteRegion_cfgEta_bound_sharedTensor
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ}
    {entry : Region Φ} (R : Fin n → τ) {blocks : Fin n → Region Φ}
    (he : Region.HasType Γ entry (List.ofFn R ++ L))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L))
    (hs : Region.HasType Γ (entry.bindBranchArguments.lsubst (Region.cfgEntryContinuations blocks)) L) :
    denoteRegion J M (.cfg R he hb) = denoteRegion J M hs := by
  obtain ⟨hl, _, _, d, dl, hk⟩ := Proofs.SSA.Isotope.LambdaSSA.Rewrite.cfg_linked_eta_common J M R he hb
  rw [denoteRegion_bound_lsubst_sharedTensor J M shared he hs hk, ← denoteRegion_linkExits J M he hl hk]
  exact (RegionDenotes.eq_denote J M d).symm.trans (RegionDenotes.eq_denote J M dl)

end SharedTensor

end Semantics.Categorical
end Silmaril.Isotope.LambdaSSA
