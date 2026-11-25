module

public import Silmaril.SSA.Isotope.LetIter.Categorical.Context.Thms
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory (snd)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (extend duplicate)
open scoped MonoidalCategory
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (caseWithContext splitMapCoprod)
open Silmaril.Isotope.LetIter.LocallyNameless (Derivation Tm)

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  (J : V ⥤ C)
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

omit [SymmetricCategory V] in
private theorem inverse_distributor_inl (R A B : V) :
    (R ◁ (coprod.inl : A ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso R A B).inv = coprod.inl := by
  let d := DistributiveTensor.leftIso R A B
  have e : coprod.inl ≫ d.hom = (R ◁ (coprod.inl : A ⟶ A ⨿ B)) :=
    DistributiveTensor.inl_leftHom R A B
  rw [← e, Category.assoc]
  change _ ≫ d.hom ≫ d.inv = _
  rw [d.hom_inv_id, Category.comp_id]

omit [SymmetricCategory V] in
private theorem inverse_distributor_inr (R A B : V) :
    (R ◁ (coprod.inr : B ⟶ A ⨿ B)) ≫ (DistributiveTensor.leftIso R A B).inv = coprod.inr := by
  let d := DistributiveTensor.leftIso R A B
  have e : coprod.inr ≫ d.hom = (R ◁ (coprod.inr : B ⟶ A ⨿ B)) :=
    DistributiveTensor.inr_leftHom R A B
  rw [← e, Category.assoc]
  change _ ≫ d.hom ≫ d.inv = _
  rw [d.hom_inv_id, Category.comp_id]

local notation "bindContext" => Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind

section
variable [DistributiveFreydCategory J]

private theorem case_inl_context {R A B D : V} (e : J.obj R ⟶ J.obj A)
    (l : J.obj (R ⊗ A) ⟶ J.obj D) (r : J.obj (R ⊗ B) ⟶ J.obj D) :
    caseWithContext J (e ≫ J.map (coprod.inl : A ⟶ A ⨿ B)) l r = bindContext J e l := by
  simp only [caseWithContext, ProofRelevant.Semantics.Categorical.bind, extend_postmap J, Category.assoc,
    ← J.map_comp_assoc, inverse_distributor_inl, splitMapCoprod,
    map_inl_inv_coprodComparison_assoc, coprod.inl_desc]

private theorem case_inr_context {R A B D : V} (e : J.obj R ⟶ J.obj B)
    (l : J.obj (R ⊗ A) ⟶ J.obj D) (r : J.obj (R ⊗ B) ⟶ J.obj D) :
    caseWithContext J (e ≫ J.map (coprod.inr : B ⟶ A ⨿ B)) l r = bindContext J e r := by
  simp only [caseWithContext, ProofRelevant.Semantics.Categorical.bind, extend_postmap J, Category.assoc,
    ← J.map_comp_assoc, inverse_distributor_inr, splitMapCoprod,
    map_inr_inv_coprodComparison_assoc, coprod.inr_desc]


theorem case_postcomp_proof {R A B D E : V} (e : J.obj R ⟶ J.obj (A ⨿ B))
    (l : J.obj (R ⊗ A) ⟶ J.obj D) (r : J.obj (R ⊗ B) ⟶ J.obj D)
    (k : J.obj D ⟶ J.obj E) :
    caseWithContext J e l r ≫ k = caseWithContext J e (l ≫ k) (r ≫ k) := by
  simp only [caseWithContext, ProofRelevant.Semantics.Categorical.bind, Category.assoc,
    coprod.desc_comp]

private theorem case_return_context [FreydCategory.CentralUnit J] {R A B : V}
    (e : J.obj R ⟶ J.obj (A ⨿ B)) :
    caseWithContext J e (J.map (snd R A ≫ coprod.inl)) (J.map (snd R B ≫ coprod.inr)) = e := by
  let d := DistributiveTensor.leftIso R A B
  let l : R ⊗ A ⟶ A ⨿ B := snd R A ≫ coprod.inl
  let r : R ⊗ B ⟶ A ⨿ B := snd R B ≫ coprod.inr
  let c := coprodComparison J (R ⊗ A) (R ⊗ B)
  have legs : coprod.desc l r = d.hom ≫ snd R (A ⨿ B) := by
    apply coprod.hom_ext
    · have left : coprod.inl ≫ d.hom = (R ◁ (coprod.inl : A ⟶ A ⨿ B)) :=
        DistributiveTensor.inl_leftHom R A B
      rw [coprod.inl_desc, ← Category.assoc, left, CartesianMonoidalCategory.whiskerLeft_snd]
    · have right : coprod.inr ≫ d.hom = (R ◁ (coprod.inr : B ⟶ A ⨿ B)) :=
        DistributiveTensor.inr_leftHom R A B
      rw [coprod.inr_desc, ← Category.assoc, right, CartesianMonoidalCategory.whiskerLeft_snd]
  have comp : coprod.desc (J.map l) (J.map r) = c ≫ J.map (coprod.desc l r) := by
    apply coprod.hom_ext
    · simp only [coprod.inl_desc, c, inl_coprodComparison_assoc, ← J.map_comp]
    · simp only [coprod.inr_desc, c, inr_coprodComparison_assoc, ← J.map_comp]
  change extend J e ≫ J.map d.inv ≫ inv c ≫ coprod.desc (J.map l) (J.map r) = e
  rw [comp, legs, IsIso.inv_hom_id_assoc, J.map_comp, ← J.map_comp_assoc,
    d.inv_hom_id, J.map_id, Category.id_comp]
  simp only [extend, CategoryTheory.PremonoidalCategory.leftTensor,
    CategoryTheory.PremonoidalCategory.id_whiskerRight, Category.id_comp, Category.assoc]
  rw [FreydCategory.whiskerLeft_snd J, ← J.map_comp_assoc]
  simp [duplicate]

end

variable [Iteration C] [ElgotCategory C] [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₅} [HasTy Φ τ] [InstructionModel J M Φ]

theorem denote_case_beta_left_proof {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B D : τ}
    (he : Derivation Φ Γ β e A) (hl : Derivation Φ Γ (.snoc β A) l D)
    (hr : Derivation Φ Γ (.snoc β B) r D) :
    denote J M (.case (.inl he) hl hr) = denote J M (.let₁ he hl) := by
  simp only [denote, Category.assoc, ← J.map_comp, Iso.inv_hom_id, Category.comp_id]
  exact case_inl_context J _ _ _

theorem denote_case_beta_right_proof {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B D : τ}
    (he : Derivation Φ Γ β e B) (hl : Derivation Φ Γ (.snoc β A) l D)
    (hr : Derivation Φ Γ (.snoc β B) r D) :
    denote J M (.case (.inr he) hl hr) = denote J M (.let₁ he hr) := by
  simp only [denote, Category.assoc, ← J.map_comp, Iso.inv_hom_id, Category.comp_id]
  exact case_inr_context J _ _ _

theorem denote_case_eta_proof [FreydCategory.CentralUnit J]
    {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {e : Tm ν Φ n} {A B : τ}
    (he : Derivation Φ Γ β e (coprod A B)) :
    denote J M (.case he (.inl (.bv (ι := 0))) (.inr (.bv (ι := 0)))) = denote J M he := by
  let R := envObj M Γ β
  let i := M.coprodIso A B
  have l : (envSnocIso M Γ β A).hom ≫ boundVar M (Γ := Γ) (β := .snoc β A) 0 =
      snd R (M.obj A) := CartesianMonoidalCategory.associator_hom_snd_snd _ _ _
  have r : (envSnocIso M Γ β B).hom ≫ boundVar M (Γ := Γ) (β := .snoc β B) 0 =
      snd R (M.obj B) := CartesianMonoidalCategory.associator_hom_snd_snd _ _ _
  simp only [denote, ← J.map_comp_assoc, l, r]
  change caseWithContext J (denote J M he ≫ J.map i.hom)
    (J.map (snd R (M.obj A)) ≫ J.map (coprod.inl ≫ i.inv))
    (J.map (snd R (M.obj B)) ≫ J.map (coprod.inr ≫ i.inv)) = _
  rw [J.map_comp, J.map_comp, ← J.map_comp_assoc, ← J.map_comp_assoc, ← case_postcomp_proof J]
  rw [case_return_context J, Category.assoc, ← J.map_comp, i.hom_inv_id, J.map_id, Category.comp_id]

end Silmaril.Isotope.LetIter.Semantics.Categorical
