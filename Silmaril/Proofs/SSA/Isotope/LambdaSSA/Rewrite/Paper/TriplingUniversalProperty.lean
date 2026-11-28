module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.Denotation.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Denotation.UniversalProperty.Thms

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Generation.Thms

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUniversalProperty

open Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory
open Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Paper.WithCaseReturns.BinaryFold.WithTripling (Step seedDenotes)
open Paper.Extension.Singleton.Generation
open Paper.Extension.Singleton (ofType)

universe u v w u₁ u₂ v₁ v₂

variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type w} [HasEff Φ ε] (pe : ε)
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V] [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C] [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J] [FreydCategory.CentralUnit J]
  (M : TypeModel τ V) [InstructionModel J M Φ] [RegionTypingCoherent (Φ := Φ) J M]
  (shared : ∀ X Y : V, ∃ h : J.obj X ⊗ J.obj Y = J.obj (X ⊗ Y),
    Functor.StrongPremonoidal.tensorIso (J := J) X Y = eqToIso h)

set_option hygiene false in
local notation "T" => Step (τ := τ) (Φ := Φ) pe
set_option hygiene false in
local notation "F" => Paper.WithCaseReturns.BinaryFold.WithTripling.denoteFunctor (Φ := Φ) pe J M shared
local notation "Obj" => ofType T
local notation "instruction" => InstructionModel.denote (J := J) (M := M)

set_option backward.isDefEq.respectTransparency false in
theorem interpretation_universal_of_generated
    (allGenerated : ∀ {A B : τ} (f : Obj A ⟶ Obj B), Generated T f)
    (G : Paper.Extension.Singleton.TypeCategory T ⥤ C) (objIso : ∀ A : τ, G.obj (Obj A) ≅ J.obj (M.obj A))
    (hG : Preserves T G objIso (Coordinates.ofModel J M))
    (hp : ∀ p : Φ, mapInCoordinates T G objIso (primitive T p) = instruction p) :
    ∃! e : F ≅ G, ∀ A : τ, e.hom.app (Obj A) = (objIso A).inv := by
  let sound : Paper.Extension.Singleton.SeedDenotes (Seed := T) J M := seedDenotes (Φ := Φ) pe J M shared
  have hF := Paper.Extension.Singleton.denoteFunctor_preserves J M shared sound
  have hprim := Paper.Extension.Singleton.denoteFunctor_map_primitive J M shared sound
  let comps (X : Paper.Extension.Singleton.TypeCategory T) : (F).obj X ≅ G.obj X :=
    (objIso (show τ from X.as)).symm
  let e : F ≅ G := NatIso.ofComponents comps (by
    intro A B f
    let a : τ := A.as
    let b : τ := B.as
    have mapEq : (F).map f = (objIso a).inv ≫ G.map f ≫ (objIso b).hom := by
      have eq := mapInCoordinates_eq_of_generated T (F) (fun A : τ => Iso.refl (J.obj (M.obj A)))
        G objIso (Coordinates.ofModel J M) hF hG (fun p => (hprim p).trans (hp p).symm)
        (allGenerated (A := a) (B := b) f)
      change 𝟙 _ ≫ (F).map f ≫ 𝟙 _ = (objIso a).inv ≫ G.map f ≫ (objIso b).hom at eq
      rwa [Category.id_comp, Category.comp_id] at eq
    change (F).map f ≫ (objIso b).inv = (objIso a).inv ≫ G.map f
    rw [mapEq]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id])
  refine ⟨e, fun _ => rfl, ?_⟩
  intro other agree
  apply Iso.ext
  apply NatTrans.ext
  funext X
  exact agree (show τ from X.as)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingUniversalProperty
