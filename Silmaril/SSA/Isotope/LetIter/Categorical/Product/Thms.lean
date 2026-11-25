module

public import Silmaril.SSA.Isotope.LetIter.Categorical.LetEta.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Product

/-! # Product equations in categorical LetIter -/

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Destructuring and immediately reconstructing a pair preserves its computation. -/
theorem denote_pair_eta {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A B : τ} (da : Derivation Φ Γ β a (product A B)) :
    denote J M (.let₂ da (.pair (.bv (ι := 1)) (.bv (ι := 0)))) = denote J M da :=
  denote_pair_eta_proof J M da

end Silmaril.Isotope.LetIter.Semantics.Categorical
