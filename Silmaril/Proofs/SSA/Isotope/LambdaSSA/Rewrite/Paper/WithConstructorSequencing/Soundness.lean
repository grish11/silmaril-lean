module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.ReturnFusion.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

/-! # Denotational soundness of the constructor sequencing steps -/

public section

universe u v m n x y

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing

open Silmaril Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open Paper.UnaryReturn
open Semantics.Categorical
open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

section Typing

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ} {L : LCtx τ} {r s : Region Φ}

theorem step_valueBranches (h : Paper.WithConstructorSequencing.Step Γ r s L) : ValueBranches Γ r L ∧ ValueBranches Γ s L := by
  cases h with
  | pair ha hb =>
    exact ⟨returnOnce_valueBranches (.pair ha.typed.1 hb.typed.1),
      .let₁ ha.typed.1 (.let₁ (hb.typed.1.rename (Ren.wk _ _))
        (.br (ℓ := 0) rfl (.pair (.var (i := 1) rfl) (.var (i := 0) rfl))))⟩
  | inl ha =>
    exact ⟨returnOnce_valueBranches (.inl ha.typed.1),
      .let₁ ha.typed.1 (.br (ℓ := 0) rfl (.inl (.var (i := 0) rfl)))⟩
  | inr ha =>
    exact ⟨returnOnce_valueBranches (.inr ha.typed.1),
      .let₁ ha.typed.1 (.br (ℓ := 0) rfl (.inr (.var (i := 0) rfl)))⟩

end Typing

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {Γ : VCtx τ}
  {L : LCtx τ} {r s : Region Φ}
  {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C]
  [SymmetricPremonoidalCategory C] [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C] [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]

theorem step_sound (e : Paper.WithConstructorSequencing.Step Γ r s L)
    (hr : HasType Γ r L) (hs : HasType Γ s L) :
    denoteRegion J M hr = denoteRegion J M hs := by
  cases e with
  | pair ha hb => exact denote_pair_boundReturn_sequencing J M (i := 0) rfl ha.typed.1 hb.typed.1
  | inl ha => exact denote_inl_boundReturn_sequencing J M (i := 0) rfl ha.typed.1
  | inr ha => exact denote_inr_boundReturn_sequencing J M (i := 0) rfl ha.typed.1

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithConstructorSequencing
