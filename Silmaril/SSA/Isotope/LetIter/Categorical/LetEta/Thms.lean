module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.LetEta

/-! # Exact categorical let-η with a central unit comparison -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₅} [HasTy Φ τ] [InstructionModel J M Φ]

/-- The denotation of binding a term and returning the new variable equals that
of the term when the Freyd unit comparison is central. -/
theorem denote_let_eta (h : IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    denote J M (.let₁ d (.bv (ι := 0))) = denote J M d :=
  denote_let_eta_proof J M h d

/-- A continuation returning unit preserves the denotation of a unit-typed
computation when the Freyd unit comparison is central. -/
theorem denote_unit_eta (h : IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n}
    (d : Derivation Φ Γ β t (unit : τ)) :
    denote J M (.let₁ d .unit) = denote J M d :=
  denote_unit_eta_proof J M h d

/-- Exact let-η holds in a model with the central-unit refinement. -/
theorem denote_let_eta_of_centralUnit [FreydCategory.CentralUnit J]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (d : Derivation Φ Γ β t A) :
    denote J M (.let₁ d (.bv (ι := 0))) = denote J M d :=
  denote_let_eta J M (FreydCategory.CentralUnit.unit_central (J := J)) d

/-- Exact unit-η holds in a model with the central-unit refinement. -/
theorem denote_unit_eta_of_centralUnit [FreydCategory.CentralUnit J]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n}
    (d : Derivation Φ Γ β t (unit : τ)) :
    denote J M (.let₁ d .unit) = denote J M d :=
  denote_unit_eta J M (FreydCategory.CentralUnit.unit_central (J := J)) d

end Silmaril.Isotope.LetIter.Semantics.Categorical
