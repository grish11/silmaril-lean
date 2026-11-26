module

public import Silmaril.SSA.Isotope.LetParIter.Categorical.Laws.Defs
public import Silmaril.SSA.Isotope.LetParIter.Substitution.Defs
public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Environment.Thms

public section

namespace Silmaril.Isotope.LetParIter.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory
open scoped MonoidalCategory
open LetIter.Semantics.Categorical
  (TypeModel ctxObj envObj boundObj boundLookup boundVar envPairHom envSnocIso dropSlot
    envRenameMap envRenameMap_free envRenameMap_bound envRenameMap_underBinder)

set_option backward.isDefEq.respectTransparency false

universe v u t q

variable {V : Type u} [Category.{v} V] [CartesianMonoidalCategory V] [HasFiniteCoproducts V]
  {τ : Type t} [TypeFormers τ] (M : TypeModel τ V) {ν : Type q} {Γ : Ctx ν τ}

private theorem bound_ext {R : V} {n : Nat} (β : BoundCtx τ n)
    (f g : R ⟶ boundObj M β)
    (slots : ∀ i : Fin n, f ≫ boundLookup M (β := β) i = g ≫ boundLookup M (β := β) i) :
    f = g := by
  induction β with
  | nil => exact SemiCartesianMonoidalCategory.toUnit_unique f g
  | snoc β A ih =>
    apply CartesianMonoidalCategory.hom_ext
    · apply ih
      intro i
      have h := slots i.succ
      change f ≫ (fst (boundObj M β) (M.obj A) ≫ boundLookup M i) =
        g ≫ (fst (boundObj M β) (M.obj A) ≫ boundLookup M i) at h
      simpa only [Category.assoc] using h
    · exact slots 0

theorem envRenameMap_succ_proof {n : Nat} (β : BoundCtx τ n) (A : τ) :
    envRenameMap M Γ (BoundCtx.Renaming.succ β A) = dropSlot M β A := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [envRenameMap_free]
    rw [dropSlot, Category.assoc]
    exact (associator_inv_fst_fst (ctxObj M Γ) (boundObj M β) (M.obj A)).symm
  · apply bound_ext M β
    intro i
    rw [Category.assoc, Category.assoc]
    change envRenameMap M Γ (BoundCtx.Renaming.succ β A) ≫ boundVar M (Γ := Γ) i =
      dropSlot M β A ≫ boundVar M (Γ := Γ) i
    rw [envRenameMap_bound]
    simp only [BoundCtx.Renaming.succ, eqToHom_refl, Category.comp_id]
    change snd _ _ ≫ fst _ _ ≫ boundLookup M i =
      ((α_ _ _ _).inv ≫ fst _ _) ≫ snd _ _ ≫ boundLookup M i
    simp only [Category.assoc, associator_inv_fst_snd_assoc]

omit [TypeFormers τ] in
private theorem leftResultRenaming_eq_succ {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    Typing.leftResultRenaming β A B = BoundCtx.Renaming.succ (.snoc β A) B := by
  have ext {r₁ r₂ : BoundCtx.Renaming (.snoc β A) (.snoc (.snoc β A) B)}
      (h : r₁.toFun = r₂.toFun) : r₁ = r₂ := by
    cases r₁
    cases r₂
    cases h
    rfl
  apply ext
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

@[reassoc] theorem envSnoc_zero {n : Nat} (β : BoundCtx τ n) (A : τ) :
    (envSnocIso M Γ β A).hom ≫ boundVar M (Γ := Γ) (β := .snoc β A) 0 =
      snd (envObj M Γ β) (M.obj A) :=
  associator_hom_snd_snd _ _ _

@[reassoc] theorem envPair_zero {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    envPairHom M Γ β A B ≫ boundVar M (Γ := Γ) (β := .snoc (.snoc β A) B) 0 =
      snd (envObj M Γ β) (M.obj A ⊗ M.obj B) ≫ snd (M.obj A) (M.obj B) := by
  change envPairHom M Γ β A B ≫ snd (ctxObj M Γ) _ ≫
    snd (boundObj M β ⊗ M.obj A) (M.obj B) = _
  simp [envPairHom, envObj]

@[reassoc] theorem envPair_one {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    envPairHom M Γ β A B ≫ boundVar M (Γ := Γ) (β := .snoc (.snoc β A) B) 1 =
      snd (envObj M Γ β) (M.obj A ⊗ M.obj B) ≫ fst (M.obj A) (M.obj B) := by
  change envPairHom M Γ β A B ≫ snd (ctxObj M Γ) _ ≫
    fst (boundObj M β ⊗ M.obj A) (M.obj B) ≫ snd (boundObj M β) (M.obj A) = _
  simp [envPairHom, envObj]

@[reassoc] theorem envPair_two {n : Nat} (β : BoundCtx τ n) (D A B : τ) :
    envPairHom M Γ (.snoc β D) A B ≫
        boundVar M (Γ := Γ) (β := .snoc (.snoc (.snoc β D) A) B) 2 =
      fst (envObj M Γ (.snoc β D)) (M.obj A ⊗ M.obj B) ≫
        boundVar M (Γ := Γ) (β := .snoc β D) 0 := by
  change envPairHom M Γ (.snoc β D) A B ≫ snd (ctxObj M Γ) _ ≫
    fst (boundObj M (.snoc β D) ⊗ M.obj A) (M.obj B) ≫
    fst (boundObj M (.snoc β D)) (M.obj A) ≫ snd (boundObj M β) (M.obj D) =
      fst (envObj M Γ (.snoc β D)) (M.obj A ⊗ M.obj B) ≫
        snd (ctxObj M Γ) (boundObj M (.snoc β D)) ≫ snd (boundObj M β) (M.obj D)
  simp [envPairHom, envObj]

private theorem pairHom_expand {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    envPairHom M Γ β A B = (α_ (envObj M Γ β) (M.obj A) (M.obj B)).inv ≫
      (envSnocIso M Γ β A).hom ▷ M.obj B ≫ (envSnocIso M Γ (.snoc β A) B).hom :=
  MonoidalCategory.pentagon_inv_hom_hom_hom_inv.symm

@[reassoc] theorem envPair_leftResult {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    envPairHom M Γ β A B ≫ envRenameMap M Γ (Typing.leftResultRenaming β A B) =
      splitContext (envObj M Γ β) (M.obj A) (M.obj B) ≫ fst _ _ ≫
        (envSnocIso M Γ β A).hom := by
  rw [leftResultRenaming_eq_succ, envRenameMap_succ_proof, pairHom_expand]
  simp only [dropSlot, splitContext, Category.assoc, Iso.hom_inv_id_assoc,
    lift_fst_assoc]
  rw [whiskerRight_fst, ← Category.assoc (α_ _ _ _).inv]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

@[reassoc] theorem envPair_underBinder {n : Nat} (β : BoundCtx τ n) (A B : τ) :
    envPairHom M Γ β A B ≫ envRenameMap M Γ (BoundCtx.Renaming.underBinder β A B) =
      splitContext (envObj M Γ β) (M.obj A) (M.obj B) ≫ snd _ _ ≫
        (envSnocIso M Γ β B).hom := by
  rw [pairHom_expand]
  simp only [Category.assoc, envRenameMap_underBinder, ← MonoidalCategory.comp_whiskerRight_assoc,
    dropSlot, Iso.hom_inv_id_assoc, splitContext, lift_snd_assoc]
  rw [← Category.assoc (α_ _ _ _).inv]
  congr 1
  apply CartesianMonoidalCategory.hom_ext <;> simp

end Silmaril.Isotope.LetParIter.Categorical
