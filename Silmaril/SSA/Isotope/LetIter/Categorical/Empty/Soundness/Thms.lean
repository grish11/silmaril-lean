module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Empty.Soundness

/-! # Categorical soundness of exact LetIter's empty-initial axiom -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : V ⥤ C)

variable [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₅} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Any two continuations following elimination of the same empty scrutinee agree.
The elimination may assign different types to the variable bound in each continuation. -/
theorem denote_emptyInitial {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)} {A A' B : τ}
    (d : Derivation Φ Γ β a (empty : τ))
    (l : Derivation Φ Γ (.snoc β A) b B) (r : Derivation Φ Γ (.snoc β A') c B) :
    denote J M (.let₁ (.abort d) l) = denote J M (.let₁ (.abort d) r) :=
  denote_emptyInitial_proof J M d l r

end Silmaril.Isotope.LetIter.Semantics.Categorical
