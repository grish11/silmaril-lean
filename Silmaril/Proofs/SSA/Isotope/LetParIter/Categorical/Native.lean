module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Defs

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits
open LetIter.Semantics.Categorical (TypeModel InstructionModel)
open scoped MonoidalCategory

universe v₁ v₂ u₁ u₂ u v w

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [∀ X Y : C, Preorder (X ⟶ Y)]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (P : FreydCategory.OrderedParallel J)
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] [InstructionModel J M Φ]

set_option backward.isDefEq.respectTransparency false in
theorem denote_embed_proof {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : LetIter.LocallyNameless.Tm ν Φ n} {A : τ}
    (d : LetIter.LocallyNameless.Derivation Φ Γ β t A) :
    denote J P M (derivation d) = LetIter.Semantics.Categorical.denote J M d := by
  induction d <;> simp only [derivation, denote, LetIter.Semantics.Categorical.denote, *]

end Silmaril.Isotope.LetParIter.Categorical
