module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Soundness.Defs
public import Silmaril.SSA.Isotope.LetParIter.Categorical.Thms
import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Soundness

/-! # Soundness of the generated mixed equivalence -/

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits
open Parallel (Derivation)
open LetIter.Semantics.Categorical (TypeModel InstructionModel)

universe u₁ u₂ v₁ v₂ u v w q

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [∀ X Y : C, Preorder (X ⟶ Y)]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (P : FreydCategory.OrderedParallel J)
  {τ : Type u} [TypeFormers τ] [Subtyping τ] (M : TypeModel τ V)
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] [InstructionModel J M Φ]
  {ε : Type q} [HasEff Φ ε] {pe : ε}

/-- Soundness of the mixed closure, reducing its native generator to the fixed
native witnesses. The uniformity case uses the induction hypothesis on its square. -/
theorem sound_of_native (L : Laws J P) (central : CentralDiagonal J)
    (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    (nativeSound : FixedNativeSound (ν := ν) J P M (Φ := Φ) pe)
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A : τ}
    {da : Derivation Φ Γ β a A} {db : Derivation Φ Γ β b A}
    (h : Equiv pe Γ da db) : denote J P M da = denote J P M db :=
  sound_of_native_proof J P M L central pureInstr nativeSound h

end Silmaril.Isotope.LetParIter.Categorical
