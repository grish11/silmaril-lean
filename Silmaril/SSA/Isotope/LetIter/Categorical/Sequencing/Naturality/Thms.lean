module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Sequencing.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Sequencing.Naturality

/-! # Native LetIter iteration naturality -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (duplicate)
open CategoryTheory CategoryTheory.Limits PremonoidalCategory CartesianMonoidalCategory
open scoped MonoidalCategory

universe u v w u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "Env" => envObj M Γ
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

/-- A continuation after a loop can run on the exit branch of each step. -/
theorem denote_iter_naturality_of_shared_tensor {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)} {A B D : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (shared : ∃ h : J.obj (Env β) ⊗ J.obj (Env β ⊗ M.obj A) = J.obj (Env β ⊗ (Env β ⊗ M.obj A)),
      tensorIso (Env β) (Env β ⊗ M.obj A) = eqToIso h)
    (da : Derivation Φ Γ β a A)
    (db : Derivation Φ Γ (.snoc β A) b (coprod B A))
    (dc : Derivation Φ Γ (.snoc β B) c D) :
    denote J M (.let₁ (.iter da db) dc) =
      denote J M (.iter da (.case db
        (.inl (dc.rename (TypedRenaming.underBinder β A B)))
        (.inr (.bv (ι := 0))))) :=
  denote_iter_naturality_of_shared_tensor_proof J M central shared da db dc

end Silmaril.Isotope.LetIter.Semantics.Categorical
