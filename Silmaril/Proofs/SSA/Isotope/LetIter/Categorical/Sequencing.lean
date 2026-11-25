module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Substitution.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Naturality.Thms

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.dsimp.instances true

public section

universe u v w u₁ u₂ v₁ v₂

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.LocallyNameless
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend retainLeft contextualLoop caseWithContext)

local notation "bindArrow" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

variable {τ : Type u} [TypeFormers τ] {ν : Type w} [DecidableEq ν]
  {Φ : Type v} [HasTy Φ τ] {Γ : Ctx ν τ}
  {V : Type u₁} {C : Type u₂} [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]

omit [DecidableEq ν] [SymmetricCategory V] [DistributiveTensor V] in
private theorem snoc_newest {n : Nat} (β : BoundCtx τ n) (A : τ) :
    (envSnocIso M Γ β A).hom ≫ boundVar M (Γ := Γ) (β := .snoc β A) 0 =
      snd (envObj M Γ β) (M.obj A) :=
  associator_hom_snd_snd (ctxObj M Γ) (boundObj M β) (M.obj A)

omit [DecidableEq ν] in
private theorem snoc_retain {n : Nat} {β : BoundCtx τ n} {A : τ} {B : V}
    (g : J.obj (M.obj A) ⟶ J.obj B) :
    J.map (envSnocIso M Γ β A).hom ≫
        extend J (J.map (boundVar M (Γ := Γ) (β := .snoc β A) 0) ≫ g) ≫
          J.map (dropSlot M β A ▷ B) =
      retainLeft J (R := envObj M Γ β) g := by
  let q : envObj M Γ (.snoc β A) ⟶ M.obj A := boundVar M 0
  change J.map (envSnocIso M Γ β A).hom ≫ extend J (J.map q ≫ g) ≫
    J.map (dropSlot M β A ▷ B) = _
  rw [extend_comp, extend_map, Category.assoc, ← retainLeft_pre_map, ← J.map_comp_assoc,
    ← J.map_comp_assoc]
  have h : (envSnocIso M Γ β A).hom ≫
      lift (𝟙 _) q ≫ (dropSlot M β A ▷ M.obj A) = 𝟙 _ := by
    apply hom_ext
    · simp [dropSlot]
    · simp [q, snoc_newest]
  rw [Category.assoc, h, J.map_id, Category.id_comp]

omit [DecidableEq ν] in
private theorem snoc_rebind {n : Nat} {β : BoundCtx τ n} {A : τ} {B : V}
    (g : J.obj (envObj M Γ β ⊗ M.obj A) ⟶ J.obj B) :
    J.map (envSnocIso M Γ β A).hom ≫
        bindArrow J (J.map (boundVar M (Γ := Γ) (β := .snoc β A) 0))
          (J.map (dropSlot M β A ▷ M.obj A) ≫ g) = g := by
  let q : envObj M Γ (.snoc β A) ⟶ M.obj A := boundVar M 0
  have h := snoc_retain J M (Γ := Γ) (β := β) (A := A) (𝟙 (J.obj (M.obj A)))
  change J.map (envSnocIso M Γ β A).hom ≫ extend J (J.map q ≫ 𝟙 _) ≫
    J.map (dropSlot M β A ▷ M.obj A) = _ at h
  change J.map (envSnocIso M Γ β A).hom ≫ extend J (J.map q) ≫
    J.map (dropSlot M β A ▷ M.obj A) ≫ g = g
  simpa only [Category.comp_id, retainLeft, leftTensor, id_whiskerRight,
    Category.id_comp, whiskerLeft_id, Iso.inv_hom_id_assoc, Category.assoc] using
      congrArg (fun k => k ≫ g) h

theorem denote_bind_op_proof {n : Nat} {β : BoundCtx τ n} {f : Φ}
    {a : Tm ν Φ n} {c : Tm ν Φ (n + 1)} {B : τ}
    (da : Derivation Φ Γ β a (instrSrc f))
    (dc : Derivation Φ Γ (.snoc β (instrTrg f)) c B) :
    denote J M (.let₁ (.op (f := f) da) dc) =
      denote J M (.let₁ da (.let₁ (.op (f := f) (.bv (ι := 0)))
        (dc.rename (TypedRenaming.underBinder β (instrSrc f) (instrTrg f))))) := by
  simp only [denote, denote_underBinder]
  unfold Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind
  rw [extend_comp]
  simpa only [Category.assoc] using
    (congrArg (fun k => extend J (denote J M da) ≫ k ≫
      J.map (envSnocIso M Γ β (instrTrg f)).hom ≫ denote J M dc)
      (snoc_retain J M (β := β) (A := instrSrc f) (InstructionModel.denote f))).symm

theorem denote_iter_bind_proof {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (da : Derivation Φ Γ β a A)
    (db : Derivation Φ Γ (.snoc β A) b (coprod B A)) :
    denote J M (.iter da db) =
      denote J M (.let₁ da (.iter (.bv (ι := 0))
        (db.rename (TypedRenaming.underBinder β A A)))) := by
  let q : envObj M Γ (.snoc β A) ⟶ M.obj A := boundVar M 0
  let k := J.map (M.coprodIso B A).hom
  change bindArrow J (denote J M da)
      (contextualLoop J (J.map (envSnocIso M Γ β A).hom ≫ denote J M db ≫ k)) =
    bindArrow J (denote J M da)
      (J.map (envSnocIso M Γ β A).hom ≫ bindArrow J (J.map q)
        (contextualLoop J (J.map (envSnocIso M Γ (.snoc β A) A).hom ≫
          denote J M (db.rename (TypedRenaming.underBinder β A A)) ≫ k)))
  rw [← Category.assoc (J.map (envSnocIso M Γ (.snoc β A) A).hom), denote_underBinder,
    Category.assoc, contextualLoop_pre_map, snoc_rebind, Category.assoc]

theorem denote_bind_case_proof {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B D : τ}
    (de : Derivation Φ Γ β e (coprod A B))
    (dl : Derivation Φ Γ (.snoc β A) l D) (dr : Derivation Φ Γ (.snoc β B) r D) :
    denote J M (.case de dl dr) =
      denote J M (.let₁ de (.case (.bv (ι := 0))
        (dl.rename (TypedRenaming.underBinder β (coprod A B) A))
        (dr.rename (TypedRenaming.underBinder β (coprod A B) B)))) := by
  let S := coprod A B
  let q : envObj M Γ (.snoc β S) ⟶ M.obj S := boundVar M 0
  let p := (M.coprodIso A B).hom
  let s := (envSnocIso M Γ β S).hom
  let dl' := dl.rename (TypedRenaming.underBinder β S A)
  let dr' := dr.rename (TypedRenaming.underBinder β S B)
  change caseWithContext J (denote J M de ≫ J.map p)
      (J.map (envSnocIso M Γ β A).hom ≫ denote J M dl)
      (J.map (envSnocIso M Γ β B).hom ≫ denote J M dr) =
    bindArrow J (denote J M de) (J.map s ≫ caseWithContext J (J.map q ≫ J.map p)
      (J.map (envSnocIso M Γ (.snoc β S) A).hom ≫ denote J M dl')
      (J.map (envSnocIso M Γ (.snoc β S) B).hom ≫ denote J M dr'))
  rw [case_bind_value, denote_underBinder, denote_underBinder, ← case_pre_map]
  have hq : s ≫ q = snd (envObj M Γ β) (M.obj S) := snoc_newest M β S
  have hs : s ≫ dropSlot M β S = fst (envObj M Γ β) (M.obj S) := by simp [s, dropSlot]
  rw [← J.map_comp_assoc s q, hq, ← J.map_comp,
    ← J.map_comp_assoc (s ▷ M.obj A), ← J.map_comp_assoc (s ▷ M.obj B),
    ← MonoidalCategory.comp_whiskerRight, ← MonoidalCategory.comp_whiskerRight, hs]

end Silmaril.Isotope.LetIter.Semantics.Categorical
