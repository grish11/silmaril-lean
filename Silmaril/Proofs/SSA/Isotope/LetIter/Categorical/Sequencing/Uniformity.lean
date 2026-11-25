module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Purity.Thms

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory PremonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (contextualLoop duplicate caseWithContext)
open scoped MonoidalCategory

universe u₁ u₂ v₁ v₂
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]

open Silmaril.Isotope.LetIter.LocallyNameless

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

universe u v w
variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "Env" => envObj M Γ
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

theorem denote_iter_uniformity_of_value_proof {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)} {A X B : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (da : Derivation Φ Γ β a A)
    (dh : Derivation Φ Γ (.snoc β A) h X)
    (db : Derivation Φ Γ (.snoc β A) b (coprod B A))
    (db' : Derivation Φ Γ (.snoc β X) b' (coprod B X))
    (u : Env (.snoc β A) ⟶ M.obj X) (pureMap : denote J M dh = J.map u)
    (square : denote J M (.case db (.inl (.bv (ι := 0)))
        (.inr (dh.rename (TypedRenaming.underBinder β A A)))) =
      denote J M ((db'.rename (TypedRenaming.underBinder β A X)).instantiate dh)) :
    denote J M (.iter da db) = denote J M (.iter (.let₁ da dh) db') := by
  let R := Env β
  let δ := BoundCtx.snoc β A
  let E := R ⊗ M.obj A
  let s := (envSnocIso M Γ β A).hom
  let t := (envSnocIso M Γ β X).hom
  let z := dropSlot M (Γ := Γ) β A
  let p := fst R (M.obj A)
  let v := s ≫ u
  let q := lift p v
  let e := denote J M db ≫ J.map (M.coprodIso B A).hom
  let f := J.map s ≫ e
  let split := (M.coprodIso B X).hom
  let g := J.map t ≫ denote J M db' ≫ J.map split
  let w : Env (.snoc δ B) ⟶ M.obj B := boundVar M 0
  let dh' := dh.rename (TypedRenaming.underBinder β A A)
  let db'' := db'.rename (TypedRenaming.underBinder β A X)
  let l : M.obj B ⟶ M.obj (coprod B X) := coprod.inl ≫ (M.coprodIso B X).inv
  let r : M.obj X ⟶ M.obj (coprod B X) := coprod.inr ≫ (M.coprodIso B X).inv
  have drop : s ≫ z = p := by simp [s, z, p, R, dropSlot]
  have left :
      J.map (s ▷ M.obj B) ≫ J.map (envSnocIso M Γ δ B).hom ≫ J.map w ≫ J.map l ≫ J.map split =
        J.map (snd E (M.obj B) ≫ coprod.inl) := by
    have newest : (envSnocIso M Γ δ B).hom ≫ w = snd (Env δ) (M.obj B) :=
      associator_hom_snd_snd (ctxObj M Γ) (boundObj M δ) (M.obj B)
    simp only [← J.map_comp]
    rw [← Category.assoc (envSnocIso M Γ δ B).hom, newest, whiskerRight_snd_assoc]
    simp [l, split, E, R, Category.assoc]
  have right :
      J.map (s ▷ M.obj A) ≫ J.map (envSnocIso M Γ δ A).hom ≫ denote J M dh' ≫ J.map r ≫ J.map split =
        J.map ((p ▷ M.obj A) ≫ v ≫ coprod.inr) := by
    rw [← Category.assoc (J.map (envSnocIso M Γ δ A).hom), denote_underBinder, pureMap]
    simp only [Category.assoc, ← J.map_comp]
    have proj : (s ▷ M.obj A) ≫ (z ▷ M.obj A) = p ▷ M.obj A := by
      rw [← MonoidalCategory.comp_whiskerRight, drop]
    rw [← Category.assoc (s ▷ M.obj A), proj]
    simp [r, split, v, Category.assoc]
    rfl
  have rhs : J.map s ≫ denote J M (db''.instantiate dh) ≫ J.map split = J.map q ≫ g := by
    rw [denote_instantiate J M dh db'' u pureMap, J.map_comp_assoc]
    simp only [Category.assoc]
    rw [← Category.assoc (J.map (envSnocIso M Γ δ X).hom), denote_underBinder]
    simp only [Category.assoc]
    have rebased : s ≫ lift (𝟙 (Env δ)) u ≫ (z ▷ M.obj X) = q := by
      apply CartesianMonoidalCategory.hom_ext
      · simp [q]
        rw [Category.id_comp, drop]
      · simp [q, v]
        exact (lift_snd p (s ≫ u)).symm
    rw [← J.map_comp_assoc (lift (𝟙 (Env δ)) u),
      ← J.map_comp_assoc s, rebased]
  have square' := congrArg (fun k => J.map s ≫ k ≫ J.map split) square
  change J.map s ≫ caseWithContext J e
      (J.map (envSnocIso M Γ δ B).hom ≫ J.map w ≫ J.map l)
      (J.map (envSnocIso M Γ δ A).hom ≫ denote J M dh' ≫ J.map r) ≫ J.map split =
    J.map s ≫ denote J M (db''.instantiate dh) ≫ J.map split at square'
  rw [← Category.assoc (J.map s), ← case_pre_map, case_postcomp, rhs] at square'
  simp only [Category.assoc] at square'
  rw [left, right] at square'
  have loopt := contextualLoop_uniformity_of_diagonal J central f g v square'
  change bindArrow J (denote J M da) (contextualLoop J f) =
    bindArrow J (bindArrow J (denote J M da) (J.map s ≫ denote J M dh)) (contextualLoop J g)
  rw [loopt, bind_assoc_capture J central, pureMap, ← J.map_comp, bind_retainEnvironment,
    retainEnvironment_map]

theorem denote_iter_uniformity_of_pure_proof {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {h b b' : Tm ν Φ (n + 1)} {A X B : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (da : Derivation Φ Γ β a A)
    (dh : Derivation Φ Γ (.snoc β A) h X)
    (db : Derivation Φ Γ (.snoc β A) b (coprod B A))
    (db' : Derivation Φ Γ (.snoc β X) b' (coprod B X))
    {ε : Type*} [HasEff Φ ε] {pe : ε}
    (pureInstr : ∀ f : Φ, IsPure pe f → ∃ p : M.obj (instrSrc f) ⟶ M.obj (instrTrg f),
      InstructionModel.denote (J := J) (M := M) f = J.map p)
    (pure : Pure pe h)
    (square : denote J M (.case db (.inl (.bv (ι := 0)))
        (.inr (dh.rename (TypedRenaming.underBinder β A A)))) =
      denote J M ((db'.rename (TypedRenaming.underBinder β A X)).instantiate dh)) :
    denote J M (.iter da db) = denote J M (.iter (.let₁ da dh) db') := by
  obtain ⟨u, hu⟩ := denote_pure_factor J M pureInstr dh pure
  exact denote_iter_uniformity_of_value_proof J M central da dh db db' u hu square

end Silmaril.Isotope.LetIter.Semantics.Categorical
