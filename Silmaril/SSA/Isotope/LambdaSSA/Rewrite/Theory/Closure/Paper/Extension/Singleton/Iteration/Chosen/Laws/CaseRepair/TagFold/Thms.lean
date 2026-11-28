module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.CaseRepair.TagFold.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Laws.CaseRepair.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Uniformity.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold

/-! # Restoring recursive outputs of a finite tag-forgetting fold -/

public section

universe u v

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.CaseRepair.TagFold

open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton

local notation "restoreBinary" => Paper.Extension.Singleton.CaseRepair.restore

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

local notation "Comp" => Paper.TypeCategory (τ := τ) Φ

/-- Folding a tagged copy leaves the retained state unchanged. -/
@[reassoc (attr := simp)]
theorem inj_fold {n : Nat} {D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (i : Fin n) : tags.inj i ≫ fold ht = 𝟙 D :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold.inj_fold ht i

/-- Restoration assigns the recursive result the current arm's input tag. -/
@[reassoc (attr := simp)]
theorem inj_restore {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (p : tags.pt ⟶ B ⨿ D) (i : Fin n) :
    tags.inj i ≫ restore ht p = tags.inj i ≫ p ≫ coprod.map (𝟙 B) (tags.inj i) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold.inj_restore ht p i

/-- Restoring and forgetting the tag preserves every observed step in standard Paper. -/
theorem restore_post {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (p : tags.pt ⟶ B ⨿ D) :
    restore ht p ≫ coprod.map (𝟙 B) (fold ht) = p :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold.restore_post ht p

/-- Recovery in standard Paper holds exactly when every arm's recurrence stays in its input copy. -/
theorem recover_iff {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (f : tags.pt ⟶ B ⨿ tags.pt) :
    restore ht (f ≫ coprod.map (𝟙 B) (fold ht)) = f ↔ PreservesTag f :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold.recover_iff ht f

/-- Discharge both obligations of binary `CaseRepair.repairSource`. Each source arm
retags its recursive result with its own injection. The fold acts as the identity
on that injection, so target restoration works for every observed step `p`. -/
theorem binary_obligations {A B D : Comp} (split : D ⨿ D ≅ A)
    (h : A ⟶ D) (f : A ⟶ B ⨿ A) (p : A ⟶ B ⨿ D)
    (hl : (coprod.inl ≫ split.hom) ≫ h = 𝟙 D)
    (hr : (coprod.inr ≫ split.hom) ≫ h = 𝟙 D)
    (left right : D ⟶ B ⨿ D)
    (fl : (coprod.inl ≫ split.hom) ≫ f = left ≫ coprod.map (𝟙 B) (coprod.inl ≫ split.hom))
    (fr : (coprod.inr ≫ split.hom) ≫ f = right ≫ coprod.map (𝟙 B) (coprod.inr ≫ split.hom)) :
    let restoreTag := restoreBinary split (coprod.inl ≫ split.hom) (coprod.inr ≫ split.hom)
    restoreTag (f ≫ coprod.map (𝟙 B) h) = f ∧
      restoreTag p ≫ coprod.map (𝟙 B) h = p :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold.binary_obligations
    split h f p hl hr left right fl fr

variable (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "J" => projection Seed

/-- In the corrected quotient, source recovery holds exactly when resetting
each arm's recursive output to its input tag preserves that arm's class. -/
theorem map_recover_iff {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (f : tags.pt ⟶ B ⨿ tags.pt) :
    (J).map (restore ht (f ≫ coprod.map (𝟙 B) (fold ht))) = (J).map f ↔
      ∀ i, (J).map ((tags.inj i ≫ f) ≫ coprod.map (𝟙 B) (fold ht ≫ tags.inj i)) =
        (J).map (tags.inj i ≫ f) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold.map_recover_iff Seed ht f

/-- Repair a corrected square by replacing the source and retaining the target and the fold. -/
theorem repairSource {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags) (f : tags.pt ⟶ B ⨿ tags.pt) (g : D ⟶ B ⨿ D)
    (arms : PreservesTag f)
    (square : projectStep Seed f ≫ coprod.map (𝟙 ((J).obj B)) ((J).map (fold ht)) =
      (J).map (fold ht) ≫ projectStep Seed g) :
    let f' := restore ht (fold ht ≫ g)
    projectStep Seed f' = projectStep Seed f ∧
      f' ≫ coprod.map (𝟙 B) (fold ht) = fold ht ≫ g :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold.repairSource Seed ht f g arms square

/-- An actual corrected commuting square gives uniformity when the source preserves tags
and the copy injections have native constructor representatives. -/
theorem uniformity {n : Nat} {B D : Comp}
    {tags : Cofan (fun _ : Fin n => D)} (ht : IsColimit tags)
    (constructor : ∀ i, Paper.TypeCategory.ConstructorReturn (tags.inj i))
    (f : tags.pt ⟶ B ⨿ tags.pt) (g : D ⟶ B ⨿ D)
    (arms : PreservesTag f)
    (square : projectStep Seed f ≫ coprod.map (𝟙 ((J).obj B)) ((J).map (fold ht)) =
      (J).map (fold ht) ≫ projectStep Seed g) :
    iterateChosen Seed (projectStep Seed f) = (J).map (fold ht) ≫ iterateChosen Seed (projectStep Seed g) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CaseRepairTagFold.uniformity Seed ht constructor f g arms square

end Silmaril.Isotope.LambdaSSA.Region.Paper.Extension.Singleton.CaseRepair.TagFold
