module

public import Silmaril.SSA.Isotope.LetIter.Categorical.LetEta.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]

open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend retainedContext)

local notation "pairArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair

omit [FreydCategory.CentralUnit J] in
private theorem pair_map {R A B : V} (f : R ⟶ A) (g : R ⟶ B) :
    pairArrow J (J.map f) (J.map g) = J.map (lift f g) := by
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.pair, retainedContext, Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind,
    ← J.map_comp, extend_map, ← Category.assoc]
  congr 1
  apply hom_ext <;> simp

omit [DecidableEq ν] [SymmetricCategory V] [DistributiveTensor V] in
private theorem envPair_components {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    envPairHom M Γ β A B ≫
      lift (boundVar M (Γ := Γ) (β := .snoc (.snoc β A) B) 1) (boundVar M 0) =
      snd (envObj M Γ β) (M.obj A ⊗ M.obj B) := by
  let δ := BoundCtx.snoc (BoundCtx.snoc β A) B
  let x : envObj M Γ δ ⟶ M.obj A := boundVar M 1
  let y : envObj M Γ δ ⟶ M.obj B := boundVar M 0
  change envPairHom M Γ β A B ≫ lift x y = _
  apply hom_ext
  · rw [Category.assoc, lift_fst]
    change ((α_ (ctxObj M Γ) (boundObj M β) (M.obj A ⊗ M.obj B)).hom ≫
          ctxObj M Γ ◁ (α_ (boundObj M β) (M.obj A) (M.obj B)).inv) ≫
        snd _ _ ≫ fst _ _ ≫ snd _ _ =
        snd (envObj M Γ β) (M.obj A ⊗ M.obj B) ≫ fst (M.obj A) (M.obj B)
    rw [Category.assoc, whiskerLeft_snd_assoc, associator_inv_fst_snd,
      associator_hom_snd_snd_assoc]
    rfl
  · rw [Category.assoc, lift_snd]
    change ((α_ (ctxObj M Γ) (boundObj M β) (M.obj A ⊗ M.obj B)).hom ≫
          ctxObj M Γ ◁ (α_ (boundObj M β) (M.obj A) (M.obj B)).inv) ≫
        snd _ _ ≫ snd _ _ =
        snd (envObj M Γ β) (M.obj A ⊗ M.obj B) ≫ snd (M.obj A) (M.obj B)
    rw [Category.assoc, whiskerLeft_snd_assoc, associator_inv_snd,
      associator_hom_snd_snd_assoc]
    rfl

theorem denote_pair_eta_proof {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A B : τ} (da : Derivation Φ Γ β a (product A B)) :
    denote J M (.let₂ da (.pair (.bv (ι := 1)) (.bv (ι := 0)))) = denote J M da := by
  let p := (M.productIso A B).hom
  let q := (M.productIso A B).inv
  let R := envObj M Γ β
  let T := M.obj (product A B)
  let β' := BoundCtx.snoc (BoundCtx.snoc β A) B
  let x : envObj M Γ β' ⟶ M.obj A := boundVar M 1
  let y : envObj M Γ β' ⟶ M.obj B := boundVar M 0
  change extend J (denote J M da) ≫ J.map (𝟙 R ⊗ₘ p) ≫
    J.map (envPairHom M Γ β A B) ≫ pairArrow J (J.map x) (J.map y) ≫ J.map q = _
  rw [pair_map]
  simp only [← J.map_comp]
  have h : (𝟙 R ⊗ₘ p) ≫ envPairHom M Γ β A B ≫ lift x y ≫ q = snd R T := by
    rw [← Category.assoc (envPairHom M Γ β A B), envPair_components, MonoidalCategory.id_tensorHom]
    change (R ◁ (M.productIso A B).hom) ≫ snd R (M.obj A ⊗ M.obj B) ≫
      (M.productIso A B).inv = snd R T
    simp [whiskerLeft_snd_assoc]
    rfl
  rw [h]
  have eta := denote_let_eta_of_centralUnit J M da
  change extend J (denote J M da) ≫
      (J.map (envSnocIso M Γ β (product A B)).hom ≫ J.map (boundVar M (Γ := Γ)
        (β := .snoc β (product A B)) 0)) = _ at eta
  rw [← J.map_comp] at eta
  have projection : (envSnocIso M Γ β (product A B)).hom ≫
      boundVar M (Γ := Γ) (β := .snoc β (product A B)) 0 = snd R T :=
    associator_hom_snd_snd (ctxObj M Γ) (boundObj M β) T
  rw [projection] at eta
  exact eta

end Silmaril.Isotope.LetIter.Semantics.Categorical
