module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs

/-! # Target generators at the selected product-return types -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic

open Silmaril Silmaril.Isotope.LambdaSSA CategoryTheory CategoryTheory.Limits
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend retainLeft)
open CartesianMonoidalCategory (fst snd toUnit)
open scoped MonoidalCategory

universe u v m n x y

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]

variable {V : Type m} {C : Type n} [Category.{x} V] [Category.{y} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  (J : V ⥤ C) [DistributiveFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

/-- Retain a copy of the input through the first computation, then run the
second computation on that copy while retaining the first result. -/
noncomputable def orderedPair {X A B : τ} (f : J.obj (M.obj X) ⟶ J.obj (M.obj A))
    (g : J.obj (M.obj X) ⟶ J.obj (M.obj B)) : J.obj (M.obj X) ⟶ J.obj (M.obj (product A B)) :=
  extend J f ≫ J.map (BraidedCategory.braiding (M.obj X) (M.obj A)).hom ≫ retainLeft J (R := M.obj A) g ≫
    J.map (M.productIso A B).inv

/-- Fold the term into the chosen target primitives and product generators. -/
noncomputable def Term.targetArrow {X D : τ} : Term Φ X D → (J.obj (M.obj X) ⟶ J.obj (M.obj D))
  | .input => 𝟙 _
  | .unit => J.map (toUnit _ ≫ M.unitIso.inv)
  | .call p a => a.targetArrow ≫ InstructionModel.denote (J := J) (M := M) p
  | .pair a b => orderedPair J M a.targetArrow b.targetArrow
  | .seq a b => a.targetArrow ≫ b.targetArrow
  | .fst A B => J.map ((M.productIso A B).hom ≫ CartesianMonoidalCategory.fst (M.obj A) (M.obj B))
  | .snd A B => J.map ((M.productIso A B).hom ≫ CartesianMonoidalCategory.snd (M.obj A) (M.obj B))
  | .destructure _ _ body => body.targetArrow

/-- Fold the region by running the product producer once, packing its value
with the original input, and continuing with the selected body. -/
noncomputable def Program.targetArrow {X D : τ} : Program Φ X D → (J.obj (M.obj X) ⟶ J.obj (M.obj D))
  | .returned t => t.targetArrow J M
  | .branchInput => 𝟙 _
  | .let₂ A B a body =>
    extend J (a.targetArrow J M) ≫ J.map (M.productIso X (product A B)).inv ≫ body.targetArrow

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic
