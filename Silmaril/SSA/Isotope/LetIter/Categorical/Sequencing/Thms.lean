module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Thms
import Silmaril.Proofs.SSA.Isotope.LetIter.Categorical.Sequencing

/-! # Sequencing in categorical LetIter -/

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
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Binding an operation is equivalent to first binding its argument, then applying the operation. -/
theorem denote_bind_op {n : Nat} {β : BoundCtx τ n} {f : Φ}
    {a : Tm ν Φ n} {c : Tm ν Φ (n + 1)} {B : τ}
    (da : Derivation Φ Γ β a (instrSrc f))
    (dc : Derivation Φ Γ (.snoc β (instrTrg f)) c B) :
    denote J M (.let₁ (.op (f := f) da) dc) =
      denote J M (.let₁ da (.let₁ (.op (f := f) (.bv (ι := 0)))
        (dc.rename (TypedRenaming.underBinder β (instrSrc f) (instrTrg f))))) :=
  denote_bind_op_proof J M da dc

/-- Iteration may first bind its initial state and then iterate from the bound value. -/
theorem denote_iter_bind {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (da : Derivation Φ Γ β a A)
    (db : Derivation Φ Γ (.snoc β A) b (coprod B A)) :
    denote J M (.iter da db) =
      denote J M (.let₁ da (.iter (.bv (ι := 0))
        (db.rename (TypedRenaming.underBinder β A A)))) :=
  denote_iter_bind_proof J M da db

end Silmaril.Isotope.LetIter.Semantics.Categorical
