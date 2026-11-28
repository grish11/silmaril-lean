module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Soundness.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Soundness.Congruence

/-! # Typing and soundness of contextual Paper extensions -/

public section

universe u v u₁ u₂ v₁ v₂

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Extension

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

open Silmaril.Isotope.LambdaSSA.Region.Paper.Extension (Eqv)

theorem typed (h : Eqv Seed Γ r s L) : HasType Γ r L ∧ HasType Γ s L := by
  induction h with
  | paper h => exact h.typed
  | extra hr hs _ => exact ⟨hr, hs⟩
  | symm _ ih => exact ih.symm
  | trans _ _ il ir => exact ⟨il.1, ir.2⟩
  | let₁ ha _ ih => exact ⟨.let₁ ha ih.1, .let₁ ha ih.2⟩
  | let₂ ha _ ih => exact ⟨.let₂ ha ih.1, .let₂ ha ih.2⟩
  | case ha _ _ il ir => exact ⟨.case ha il.1 ir.1, .case ha il.2 ir.2⟩
  | cfg R _ _ ie ib => exact ⟨.cfg R ie.1 (fun i => (ib i).1), .cfg R ie.2 (fun i => (ib i).2)⟩
  | lsubstCongr hp _ ih =>
    exact ⟨hp.hasType.lsubst (fun _ _ hi => (ih hi).1),
      hp.hasType.lsubst (fun _ _ hi => (ih hi).2)⟩
  | lsubstPost _ hr hs hσ _ => exact ⟨hr.hasType.lsubst hσ, hs.hasType.lsubst hσ⟩
  | substVars _ hθ ih =>
    have ht : Tm.Subst.HasType _ _ _ := fun _ _ hi => (hθ hi).hasType
    exact ⟨ih.1.substVars ht, ih.2.substVars ht⟩
  | renameLabels _ hρ ih => exact ⟨ih.1.renameLabels hρ, ih.2.renameLabels hρ⟩

theorem toPaper (sound : ∀ {Γ L r s}, Seed Γ r s L → Paper.Eqv Γ r s L)
    (h : Eqv Seed Γ r s L) : Paper.Eqv Γ r s L := by
  induction h with
  | paper h => exact h
  | extra _ _ step => exact sound step
  | symm _ ih => exact ih.symm
  | trans _ _ ih ij => exact ih.trans ij
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ il ir => exact .case ha il ir
  | cfg R _ _ ie ib => exact .cfg R ie ib
  | lsubstCongr hp _ ih => exact .lsubstCongr hp ih
  | lsubstPost _ hr hs hσ ih => exact .lsubstPost ih hr hs hσ
  | substVars _ hθ ih => exact .substVars ih hθ
  | renameLabels _ hρ ih => exact .renameLabels ih hρ

theorem mapSeed {Target : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop}
    (incl : ∀ {Γ r s L}, Seed Γ r s L → Target Γ r s L)
    (h : Paper.Extension.Eqv Seed Γ r s L) : Paper.Extension.Eqv Target Γ r s L := by
  induction h with
  | paper h => exact .paper h
  | extra hr hs h => exact .extra hr hs (incl h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | let₁ ha _ ih => exact .let₁ ha ih
  | let₂ ha _ ih => exact .let₂ ha ih
  | case ha _ _ ihl ihr => exact .case ha ihl ihr
  | cfg R _ _ ihe ihb => exact .cfg R ihe ihb
  | lsubstCongr hp _ ih => exact .lsubstCongr hp ih
  | lsubstPost _ hr hs hσ ih => exact .lsubstPost ih hr hs hσ
  | substVars _ hθ ih => exact .substVars ih hθ
  | renameLabels _ hρ ih => exact .renameLabels ih hρ

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

set_option backward.isDefEq.respectTransparency false in
private theorem common
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    (seedDenotes : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Seed Γ r s L →
      ∀ (hr : HasType Γ r L) (hs : HasType Γ s L),
        ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f)
    (h : Eqv Seed Γ r s L) : CommonDenotation J M Γ r s L := by
  induction h with
  | paper h => exact CommonDenotation.of_eq (h.sound J M shared h.typed.1 h.typed.2)
  | extra hr hs h =>
    obtain ⟨f, dr, ds⟩ := seedDenotes h hr hs
    exact ⟨hr, hs, f, dr, ds⟩
  | symm _ ih => exact ih.symm
  | trans _ _ il ir => exact il.trans ir
  | let₁ ha _ ih => exact CommonDenotation.let₁ ha ih
  | let₂ ha _ ih => exact CommonDenotation.let₂ ha ih
  | case ha _ _ il ir => exact CommonDenotation.case ha il ir
  | cfg R _ _ ie ib => exact CommonDenotation.cfg R ie ib
  | lsubstCongr hp _ ih => exact CommonDenotation.lsubstCongr shared hp ih
  | lsubstPost _ hr hs hσ ih => exact ih.lsubstPost shared hr hs hσ
  | substVars _ hθ ih => exact ih.substVars hθ
  | renameLabels _ hρ ih => exact ih.renameLabels hρ

theorem denotes
    (shared : ∀ E X : V, ∃ h : J.obj E ⊗ J.obj X = J.obj (E ⊗ X),
      Functor.StrongPremonoidal.tensorIso (J := J) E X = eqToIso h)
    (seedDenotes : ∀ {Γ : VCtx τ} {r s : Region Φ} {L : LCtx τ}, Seed Γ r s L →
      ∀ (hr : HasType Γ r L) (hs : HasType Γ s L),
        ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f)
    (h : Eqv Seed Γ r s L) :
    ∃ f, RegionDenotes J M (typed h).1 f ∧ RegionDenotes J M (typed h).2 f := by
  obtain ⟨_, _, f, dr, ds⟩ := common J M shared seedDenotes h
  exact ⟨f, dr, ds⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.Extension
