module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Iteration.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Sequencing.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Case.Thms

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
variable [FreydCategory.CentralUnit J]
  {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  (M : TypeModel τ V) [InstructionModel J M Φ]
local notation "Env" => envObj M Γ
local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)

theorem denote_iter_codiagonal_of_shared_tensor_proof {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (central : IsCentral (J.map (duplicate (Env β)) ≫ (tensorIso (Env β) (Env β)).inv))
    (shared : ∃ h : J.obj (Env β) ⊗ J.obj (Env β ⊗ M.obj A) = J.obj (Env β ⊗ (Env β ⊗ M.obj A)),
      tensorIso (Env β) (Env β ⊗ M.obj A) = eqToIso h)
    (da : Derivation Φ Γ β a A)
    (db : Derivation Φ Γ (.snoc β A) b (coprod (coprod B A) A)) :
    denote J M (.iter da (.iter (.bv (ι := 0))
      (db.rename (TypedRenaming.underBinder β A A)))) =
      denote J M (.iter da (.case db (.bv (ι := 0)) (.inr (.bv (ι := 0))))) := by
  let H := coprod B A
  let R := Env β
  let δ := BoundCtx.snoc β A
  let E := R ⊗ M.obj A
  let s := (envSnocIso M Γ β A).hom
  let e := (M.coprodIso B A).hom
  let rawBody := denote J M db ≫ J.map (M.coprodIso H A).hom
  let f := J.map s ≫ rawBody
  let g := f ≫ J.map (coprod.map e (𝟙 (M.obj A)))
  let l : Env (.snoc δ H) ⟶ M.obj H := boundVar M 0
  let r : Env (.snoc δ A) ⟶ M.obj A := boundVar M 0
  let inj : M.obj A ⟶ M.obj H := coprod.inr ≫ (M.coprodIso B A).inv
  change bindArrow J (denote J M da) (contextualLoop J
      (J.map s ≫ denote J M (.iter (.bv (ι := 0))
        (db.rename (TypedRenaming.underBinder β A A))) ≫ J.map e)) =
    bindArrow J (denote J M da) (contextualLoop J
      (J.map s ≫ caseWithContext J rawBody
        (J.map (envSnocIso M Γ δ H).hom ≫ J.map l)
        (J.map (envSnocIso M Γ δ A).hom ≫ J.map r ≫ J.map inj) ≫ J.map e))
  have leftProjection {X : τ} (q : Env (.snoc δ X) ⟶ M.obj X)
      (h : q = boundVar M 0) :
      (s ▷ M.obj X) ≫ (envSnocIso M Γ δ X).hom ≫ q = snd E (M.obj X) := by
    have newest : (envSnocIso M Γ δ X).hom ≫ q = snd (Env δ) (M.obj X) :=
      (congrArg (fun m => (envSnocIso M Γ δ X).hom ≫ m) h).trans
        (associator_hom_snd_snd (ctxObj M Γ) (boundObj M δ) (M.obj X))
    rw [newest, whiskerRight_snd]
  have left : J.map (s ▷ M.obj H) ≫ J.map (envSnocIso M Γ δ H).hom ≫ J.map l ≫ J.map e =
      J.map (snd E (M.obj H) ≫ e) := by
    simp only [← J.map_comp]
    rw [← Category.assoc (envSnocIso M Γ δ H).hom, ← Category.assoc (s ▷ M.obj H),
      leftProjection l rfl]
  have right : J.map (s ▷ M.obj A) ≫ J.map (envSnocIso M Γ δ A).hom ≫ J.map r ≫ J.map inj ≫ J.map e =
      J.map (snd E (M.obj A) ≫ coprod.inr) := by
    simp only [← J.map_comp]
    rw [← Category.assoc (envSnocIso M Γ δ A).hom,
      ← Category.assoc (s ▷ M.obj A), leftProjection r rfl]
    simp [inj, e]
  rw [← Category.assoc (J.map s), denote_iter_newest,
    ← contextualLoop_map_value_exit,
    ← Category.assoc (J.map s) (caseWithContext J rawBody _ _) (J.map e),
    ← case_pre_map, case_postcomp]
  simp only [Category.assoc]
  rw [left, right, case_return_map]
  have align : g = J.map (envSnocIso M Γ β A).hom ≫ denote J M db ≫
      J.map (M.coprodIso H A).hom ≫ J.map (coprod.map e (𝟙 (M.obj A))) := by
    simp only [g, f, rawBody, Category.assoc]
    rfl
  rw [← align]
  change bindArrow J (denote J M da) (contextualLoop J (contextualLoop J g)) =
    bindArrow J (denote J M da) (contextualLoop J (f ≫ J.map (coprod.desc e coprod.inr)))
  rw [contextualLoop_codiagonal J central shared]
  simp only [g, Category.assoc, ← J.map_comp]
  congr 4
  apply coprod.hom_ext <;> simp

end Silmaril.Isotope.LetIter.Semantics.Categorical
