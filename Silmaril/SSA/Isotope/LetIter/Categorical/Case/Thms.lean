module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Case

/-! # Case β and η laws for categorical exact LetIter -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : V ⥤ C)
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₅} [HasTy Φ τ] [InstructionModel J M Φ]

/-- The left injection selects the left continuation after evaluating its argument. -/
theorem denote_case_beta_left {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B D : τ}
    (he : Derivation Φ Γ β e A) (hl : Derivation Φ Γ (.snoc β A) l D)
    (hr : Derivation Φ Γ (.snoc β B) r D) :
    denote J M (.case (.inl he) hl hr) = denote J M (.let₁ he hl) :=
  denote_case_beta_left_proof J M he hl hr

/-- The right injection selects the right continuation after evaluating its argument. -/
theorem denote_case_beta_right {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B D : τ}
    (he : Derivation Φ Γ β e B) (hl : Derivation Φ Γ (.snoc β A) l D)
    (hr : Derivation Φ Γ (.snoc β B) r D) :
    denote J M (.case (.inr he) hl hr) = denote J M (.let₁ he hr) :=
  denote_case_beta_right_proof J M he hl hr

/-- Branching and immediately returning the selected injection preserves the computation. -/
theorem denote_case_eta [FreydCategory.CentralUnit J]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {e : Tm ν Φ n} {A B : τ}
    (he : Derivation Φ Γ β e (coprod A B)) :
    denote J M (.case he (.inl (.bv (ι := 0))) (.inr (.bv (ι := 0)))) = denote J M he :=
  denote_case_eta_proof J M he

end Silmaril.Isotope.LetIter.Semantics.Categorical
