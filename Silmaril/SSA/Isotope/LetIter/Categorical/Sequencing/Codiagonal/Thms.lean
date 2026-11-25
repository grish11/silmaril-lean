module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Sequencing.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Sequencing.Codiagonal

/-! # Native LetIter iteration codiagonal -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory PremonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (duplicate)
open scoped MonoidalCategory

universe u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

open Silmaril.Isotope.LetIter.LocallyNameless

universe u v w
variable [FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  (M : TypeModel τ V) [InstructionModel J M Φ]
local notation "Env" => envObj M Γ
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

/-- Collapse two native loops on the same state to one loop. -/
theorem denote_iter_codiagonal_of_shared_tensor {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (shared : ∃ h : J.obj (Env β) ⊗ J.obj (Env β ⊗ M.obj A) = J.obj (Env β ⊗ (Env β ⊗ M.obj A)),
      tensorIso (Env β) (Env β ⊗ M.obj A) = eqToIso h)
    (da : Derivation Φ Γ β a A)
    (db : Derivation Φ Γ (.snoc β A) b (coprod (coprod B A) A)) :
    denote J M (.iter da (.iter (.bv (ι := 0))
      (db.rename (TypedRenaming.underBinder β A A)))) =
      denote J M (.iter da (.case db (.bv (ι := 0)) (.inr (.bv (ι := 0))))) :=
  denote_iter_codiagonal_of_shared_tensor_proof J M central shared da db

end Silmaril.Isotope.LetIter.Semantics.Categorical
