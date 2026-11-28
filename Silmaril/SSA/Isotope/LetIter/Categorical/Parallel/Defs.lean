module

public import Silmaril.Semantics.Categories.Freyd.Parallel.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Thms

/-! # Shared-context parallel on native LetIter derivations -/

@[expose] public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open LocallyNameless (Derivation)
open scoped MonoidalCategory

universe u₁ u₂ u v w v₁ v₂

variable {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] [∀ X Y : C, Preorder (X ⟶ Y)]
  (J : V ⥤ C) [StrongElgotFreydCategory J] (P : FreydCategory.OrderedParallel J)
  {τ : Type u} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type v} [DecidableEq ν] {Φ : Type w} [HasTy Φ τ] [InstructionModel J M Φ]

/-- Interpret two native branches in parallel on the same free and bound environment.
The result uses the product comparison of the native type interpretation. -/
noncomputable def denotePar {Γ : Ctx ν τ} {n : Nat} {β : Isotope.BoundCtx τ n}
    {s t : LocallyNameless.Tm ν Φ n} {A B : τ}
    (ds : Derivation Φ Γ β s A) (dt : Derivation Φ Γ β t B) :
    J.obj (envObj M Γ β) ⟶ J.obj (M.obj (product A B)) :=
  P.par (denote J M ds) (denote J M dt) ≫ J.map (M.productIso A B).inv

end Silmaril.Isotope.LetIter.Semantics.Categorical
