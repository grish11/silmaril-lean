module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open CategoryTheory.CartesianMonoidalCategory (snd)
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend)
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

private def tensorEmptyIsInitial {V : Type u₁} [Category.{v₁} V]
    [CartesianMonoidalCategory V] [HasBinaryCoproducts V] [DistributiveTensor V]
    (R Z : V) (initial : IsInitial Z) : IsInitial (R ⊗ Z) := by
  have injections : (coprod.inl : R ⊗ Z ⟶ (R ⊗ Z) ⨿ (R ⊗ Z)) = coprod.inr := by
    apply (cancel_mono (DistributiveTensor.leftHom R Z Z)).mp
    rw [DistributiveTensor.inl_leftHom, DistributiveTensor.inr_leftHom,
      initial.hom_ext (coprod.inl : Z ⟶ Z ⨿ Z) coprod.inr]
  refine IsInitial.ofUniqueHom (fun X => snd R Z ≫ initial.to X) (fun X f => ?_)
  let g := snd R Z ≫ initial.to X
  exact (coprod.inl_desc f g).symm.trans
    ((congrArg (fun h => h ≫ coprod.desc f g) injections).trans (coprod.inr_desc f g))

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

theorem denote_emptyInitial_proof {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)} {A A' B : τ}
    (d : Derivation Φ Γ β a (empty : τ))
    (l : Derivation Φ Γ (.snoc β A) b B) (r : Derivation Φ Γ (.snoc β A') c B) :
    denote J M (.let₁ (.abort d) l) = denote J M (.let₁ (.abort d) r) := by
  let R := envObj M Γ β
  let Z := M.obj (empty : τ)
  let init : IsInitial (J.obj (R ⊗ Z)) :=
    (tensorEmptyIsInitial R Z M.emptyIsInitial).isInitialObj J _
  let left : J.obj (R ⊗ Z) ⟶ J.obj (M.obj B) :=
    J.map (R ◁ M.emptyIsInitial.to (M.obj A)) ≫
      J.map (envSnocIso M Γ β A).hom ≫ denote J M l
  let right : J.obj (R ⊗ Z) ⟶ J.obj (M.obj B) :=
    J.map (R ◁ M.emptyIsInitial.to (M.obj A')) ≫
      J.map (envSnocIso M Γ β A').hom ≫ denote J M r
  simp only [denote, ProofRelevant.Semantics.Categorical.bind,
    extend_postmap J, Category.assoc]
  exact congrArg (fun k => extend J (denote J M d) ≫ k) (init.hom_ext left right)

end Silmaril.Isotope.LetIter.Semantics.Categorical
