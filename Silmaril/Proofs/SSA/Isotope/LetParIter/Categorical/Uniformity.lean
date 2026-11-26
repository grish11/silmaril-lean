module

public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Iteration
public import Silmaril.Proofs.SSA.Isotope.LetParIter.Categorical.Substitution
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory PremonoidalCategory
open scoped MonoidalCategory
open Parallel (Derivation)
open LetIter.Semantics.Categorical
  (TypeModel InstructionModel envObj envSnocIso boundVar dropSlot case_pre_map case_postcomp
    contextualLoop_uniformity_of_diagonal bind_assoc_capture bind_retainEnvironment retainEnvironment_map)
open LetIter.ProofRelevant.Semantics.Categorical (duplicate caseWithContext contextualLoop)

local notation "bindArrow" => LetIter.ProofRelevant.Semantics.Categorical.bind

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
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

local notation "Env" => envObj M Γ
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)
set_option backward.isDefEq.respectTransparency false

theorem iterUniformity_sound_proof {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)} {A X B : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (da : Derivation Φ Γ β a A) (dh : Derivation Φ Γ (.snoc β A) h X)
    (db : Derivation Φ Γ (.snoc β A) b (coprod B A))
    (db' : Derivation Φ Γ (.snoc β X) b' (coprod B X))
    (u : Env (.snoc β A) ⟶ M.obj X) (hu : denote J P M dh = J.map u)
    (square : denote J P M (Typing.uniformityLeft db dh) = denote J P M (Typing.uniformityRight db' dh)) :
    denote J P M (.iter (h := rfl) da db) = denote J P M (.iter (h := rfl) (.let₁ da dh) db') := by
  let R := Env β
  let δ := β.snoc A
  let E := R ⊗ M.obj A
  let s := (envSnocIso M Γ β A).hom
  let t := (envSnocIso M Γ β X).hom
  let p := fst R (M.obj A)
  let v := s ≫ u
  let split := (M.coprodIso B X).hom
  let e := denote J P M db ≫ J.map (M.coprodIso B A).hom
  let f := J.map s ≫ e
  let g := J.map t ≫ denote J P M db' ≫ J.map split
  let w : Env (.snoc δ B) ⟶ M.obj B := boundVar M 0
  let l : M.obj B ⟶ M.obj (coprod B X) := coprod.inl ≫ (M.coprodIso B X).inv
  let r : M.obj X ⟶ M.obj (coprod B X) := coprod.inr ≫ (M.coprodIso B X).inv
  have drop : s ≫ dropSlot M β A = p := by simp [s, p, R, dropSlot]
  have left :
      J.map (s ▷ M.obj B) ≫ J.map (envSnocIso M Γ δ B).hom ≫ J.map w ≫ J.map l ≫ J.map split =
        J.map (snd E (M.obj B) ≫ coprod.inl) := by
    simp only [← J.map_comp]
    rw [← Category.assoc (envSnocIso M Γ δ B).hom, envSnoc_zero, whiskerRight_snd_assoc]
    simp [l, split, E, R, Category.assoc]
  have right : J.map (s ▷ M.obj A) ≫ J.map (envSnocIso M Γ δ A).hom ≫
      denote J P M (Typing.underBinder dh) ≫ J.map r ≫ J.map split =
        J.map ((p ▷ M.obj A) ≫ v ≫ coprod.inr) := by
    rw [← Category.assoc (J.map (envSnocIso M Γ δ A).hom), denote_underBinder_proof, hu]
    simp only [Category.assoc, ← J.map_comp]
    rw [← MonoidalCategory.comp_whiskerRight_assoc, drop]
    simp [r, split, v, Category.assoc]
    rfl
  have rhs : J.map s ≫ denote J P M (Typing.uniformityRight db' dh) ≫ J.map split =
      J.map (lift p v) ≫ g := by
    rw [Typing.uniformityRight, denote_instantiate_proof J P M dh _ u hu, J.map_comp_assoc]
    simp only [Category.assoc]
    rw [← Category.assoc (J.map (envSnocIso M Γ δ X).hom), denote_underBinder_proof]
    simp only [Category.assoc]
    have rebased : s ≫ lift (𝟙 (Env δ)) u ≫ (dropSlot M β A ▷ M.obj X) = lift p v := by
      apply CartesianMonoidalCategory.hom_ext
      · simp
        rw [Category.id_comp, drop]
      · simp [v]
        exact (lift_snd p (s ≫ u)).symm
    rw [← J.map_comp_assoc (lift (𝟙 (Env δ)) u), ← J.map_comp_assoc s, rebased]
  have square' := congrArg (fun k => J.map s ≫ k ≫ J.map split) square
  change J.map s ≫ caseWithContext J e
      (J.map (envSnocIso M Γ δ B).hom ≫ J.map w ≫ J.map l)
      (J.map (envSnocIso M Γ δ A).hom ≫ denote J P M (Typing.underBinder dh) ≫ J.map r) ≫ J.map split =
    J.map s ≫ denote J P M (Typing.uniformityRight db' dh) ≫ J.map split at square'
  rw [← Category.assoc (J.map s), ← case_pre_map, case_postcomp, rhs] at square'
  simp only [Category.assoc] at square'
  rw [left, right] at square'
  have loopEq := contextualLoop_uniformity_of_diagonal J central f g v square'
  change bindArrow J (denote J P M da) (contextualLoop J f) =
    bindArrow J (bindArrow J (denote J P M da) (J.map s ≫ denote J P M dh)) (contextualLoop J g)
  rw [loopEq, bind_assoc_capture J central, hu, ← J.map_comp, bind_retainEnvironment,
    retainEnvironment_map]

end Silmaril.Isotope.LetParIter.Categorical
