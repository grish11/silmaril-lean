module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext contextualLoop duplicate)
open CategoryTheory CategoryTheory.Limits PremonoidalCategory CartesianMonoidalCategory
open scoped MonoidalCategory

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

universe u v w u₁ u₂ v₁ v₂
variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  [FreydCategory.CentralUnit J] (M : TypeModel τ V) [InstructionModel J M Φ]

local notation "Env" => envObj M Γ
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

theorem denote_iter_naturality_of_shared_tensor_proof {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b c : Tm ν Φ (n + 1)} {A B D : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (shared : ∃ h : J.obj (Env β) ⊗ J.obj (Env β ⊗ M.obj A) = J.obj (Env β ⊗ (Env β ⊗ M.obj A)),
      tensorIso (Env β) (Env β ⊗ M.obj A) = eqToIso h)
    (da : Derivation Φ Γ β a A)
    (db : Derivation Φ Γ (.snoc β A) b (coprod B A))
    (dc : Derivation Φ Γ (.snoc β B) c D) :
    denote J M (.let₁ (.iter da db) dc) =
      denote J M (.iter da (.case db
        (.inl (dc.rename (TypedRenaming.underBinder β A B)))
        (.inr (.bv (ι := 0))))) := by
  let R := Env β
  let δ := BoundCtx.snoc β A
  let E := R ⊗ M.obj A
  let s := (envSnocIso M Γ β A).hom
  let e := denote J M db ≫ J.map (M.coprodIso B A).hom
  let f := J.map s ≫ e
  let k := J.map (envSnocIso M Γ β B).hom ≫ denote J M dc
  let q : Env (.snoc δ A) ⟶ M.obj A := boundVar M 0
  let dc' := dc.rename (TypedRenaming.underBinder β A B)
  let incl : M.obj D ⟶ M.obj (coprod D A) := coprod.inl ≫ (M.coprodIso D A).inv
  let incr : M.obj A ⟶ M.obj (coprod D A) := coprod.inr ≫ (M.coprodIso D A).inv
  let split := (M.coprodIso D A).hom
  have project : s ≫ dropSlot M β A = fst R (M.obj A) := by simp [s, dropSlot, R]
  have left :
      J.map (s ▷ M.obj B) ≫ J.map (envSnocIso M Γ δ B).hom ≫ denote J M dc' ≫
        J.map incl ≫ J.map split =
      J.map (fst R (M.obj A) ▷ M.obj B) ≫ k ≫ J.map coprod.inl := by
    rw [← Category.assoc (J.map (envSnocIso M Γ δ B).hom), denote_underBinder, Category.assoc,
      ← J.map_comp_assoc (s ▷ M.obj B), ← MonoidalCategory.comp_whiskerRight, project, ← J.map_comp]
    have h : incl ≫ split = coprod.inl := by simp [incl, split]
    rw [h]
  have right :
      J.map (s ▷ M.obj A) ≫ J.map (envSnocIso M Γ δ A).hom ≫ J.map q ≫ J.map incr ≫ J.map split =
      J.map (snd E (M.obj A) ≫ coprod.inr) := by
    simp only [← J.map_comp]
    have projection : (envSnocIso M Γ δ A).hom ≫ q = snd (Env δ) (M.obj A) :=
      associator_hom_snd_snd (ctxObj M Γ) (boundObj M δ) (M.obj A)
    rw [← Category.assoc (envSnocIso M Γ δ A).hom, projection,
      whiskerRight_snd_assoc]
    simp [incr, split, Category.assoc, E, R]
  change bindArrow J (bindArrow J (denote J M da) (contextualLoop J f)) k =
    bindArrow J (denote J M da) (contextualLoop J
      (J.map s ≫ caseWithContext J e
        (J.map (envSnocIso M Γ δ B).hom ≫ (denote J M dc' ≫ J.map incl))
        (J.map (envSnocIso M Γ δ A).hom ≫ (J.map q ≫ J.map incr)) ≫ J.map split))
  rw [bind_assoc_capture J central, contextualLoop_naturality J central shared,
    ← Category.assoc (J.map s), ← case_pre_map, case_postcomp]
  simp only [Category.assoc]
  rw [left, right]

end Silmaril.Isotope.LetIter.Semantics.Categorical
