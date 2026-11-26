module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Laws.Defs
public import Silmaril.SSA.Isotope.LetParIter.Equations.Defs

/-! # Semantic premises for the mixed congruence -/

@[expose] public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open LetIter.ProofRelevant.Semantics.Categorical (duplicate)

universe u₁ u₂ v₁ v₂ u v w q

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : V ⥤ C)

/-- Centrality of the pure diagonal transported to the computation tensor.
This is the arrow-level hypothesis used by contextual uniformity. -/
def CentralDiagonal [FreydCategory J] : Prop :=
  ∀ R : V, PremonoidalCategory.IsCentral
    (J.map (duplicate R) ≫ (Functor.StrongPremonoidal.tensorIso (J := J) R R).inv)

variable [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [∀ X Y : C, Preorder (X ⟶ Y)]
  [StrongElgotFreydCategory J] (P : FreydCategory.OrderedParallel J)
  {τ : Type u} [TypeFormers τ] [Subtyping τ] (M : TypeModel τ V)
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] [InstructionModel J M Φ]
  {ε : Type q} [HasEff Φ ε]

/-- The native obligation for a mixed evaluator concerns only the embedded, fixed
witnesses of the proof-relevant equation. -/
def FixedNativeSound (pe : ε) : Prop :=
  ∀ {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a b : LetIter.LocallyNameless.Tm ν Φ n} {A : τ}
    (da : LetIter.LocallyNameless.Derivation Φ Γ β a A)
    (db : LetIter.LocallyNameless.Derivation Φ Γ β b A),
    LetIter.ProofRelevant.LocallyNameless.TypedEquiv.Related pe Γ
      (nativeTyping da) (nativeTyping db) →
    denote J P M (derivation da) = denote J P M (derivation db)

end Silmaril.Isotope.LetParIter.Categorical
