module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.LabelRenaming.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Combinators
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Labels

/-! # Outward CFGs with arbitrary typed entries -/

public section

universe v₁ v₂ u₁ u₂ u₃ u₄

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite

open CategoryTheory CategoryTheory.Limits CategoryTheory.PremonoidalCategory
open scoped MonoidalCategory
open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Semantics.Categorical
open Silmaril.Isotope.LetIter.Semantics.Categorical (TypeModel InstructionModel)
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical
  (caseWithContext duplicate extend retainLeft contextualLoop splitMapCoprod)
open CategoryTheory.CartesianMonoidalCategory (snd toUnit)

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]

section Freyd

variable (J : V ⥤ C) [DistributiveFreydCategory J]

local notation "tensorIso" => Functor.StrongPremonoidal.tensorIso (J := J)
local notation "unitIso" => Functor.StrongPremonoidal.unitIso (J := J)

private theorem map_snd {E A : V} :
    (tensorIso E A).hom ≫ J.map (snd E A) =
      (J.map (toUnit E) ≫ (unitIso).inv) ▷ J.obj A ≫ (λ_ (J.obj A)).hom := by
  rw [← CartesianMonoidalCategory.whiskerRight_toUnit_comp_leftUnitor_hom, J.map_comp,
    ← Category.assoc, ← Functor.StrongPremonoidal.tensor_naturality_left, Category.assoc,
    PremonoidalCategory.comp_whiskerRight, Category.assoc, ← Functor.StrongPremonoidal.left_unitality]
  have h : (unitIso).inv ▷ J.obj A ≫ (unitIso).hom ▷ J.obj A = 𝟙 _ :=
    (whiskerRightIso unitIso (J.obj A)).inv_hom_id
  rw [← Category.assoc ((unitIso).inv ▷ J.obj A), h, Category.id_comp]

theorem retainLeft_snd (hu : IsCentral (unitIso).hom) {E A B : V} (f : J.obj A ⟶ J.obj B) :
    retainLeft J (R := E) f ≫ J.map (snd E B) = J.map (snd E A) ≫ f := by
  apply (cancel_epi (tensorIso E A).hom).1
  have hd := (FreydCategory.image_central J (toUnit E)).comp (IsCentral.inv unitIso hu)
  have he := hd.1 f
  simp only [leftTensor, rightTensor] at he
  simp only [retainLeft, leftTensor, Category.assoc, Iso.hom_inv_id_assoc,
    id_whiskerRight, Category.id_comp, map_snd J]
  rw [← Category.assoc, ← he, Category.assoc, PremonoidalCategory.leftUnitor_naturality,
    ← Category.assoc, ← map_snd J, Category.assoc]

theorem extend_snd (hu : IsCentral (unitIso).hom) {E A : V} (f : J.obj E ⟶ J.obj A) :
    extend J f ≫ J.map (snd E A) = f := by
  rw [extend_eq_retainLeft, Category.assoc, retainLeft_snd J hu, ← J.map_comp_assoc]
  simp [duplicate]

end Freyd

section Cfg

variable [Iteration C] [ElgotCategory C] (J : V ⥤ C) [StrongElgotFreydCategory J]
  {τ : Type u₃} [TypeFormers τ] (M : TypeModel τ V)
  {Φ : Type u₄} [HasTy Φ τ] [InstructionModel J M Φ]

/-- A dispatcher whose body always exits runs the body exactly once. -/
theorem contextualLoop_once
    (hu : IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {E A B : V} (f : J.obj (E ⊗ A) ⟶ J.obj B) :
    contextualLoop J (f ≫ J.map (coprod.inl : B ⟶ B ⨿ A)) = f := by
  let keep : E ⊗ A ⟶ E ⊗ (E ⊗ A) :=
    CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst E A) (𝟙 _)
  let beforeExit := J.map keep ≫ retainLeft J (R := E) f
  have firstStep : contextualLoop J (f ≫ J.map (coprod.inl : B ⟶ B ⨿ A)) =
      iterate (beforeExit ≫ (coprod.inl : J.obj (E ⊗ B) ⟶ J.obj (E ⊗ B) ⨿ J.obj (E ⊗ A))) ≫
        J.map (snd E B) := by
    simp only [contextualLoop, retainLeft_comp, retainLeft_map, Category.assoc,
      distributeMap_inl J E B A, beforeExit, keep]
  rw [firstStep, ElgotCategory.fixpoint_assoc, Category.assoc, coprod.inl_desc_assoc,
    Category.id_comp]
  simp only [beforeExit, Category.assoc, retainLeft_snd J hu, ← J.map_comp_assoc, keep,
    CartesianMonoidalCategory.lift_snd, J.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem outwardLabelMap {n : Nat} (R : Fin n → τ) (L : LCtx τ)
    (hρ : Ren L (List.ofFn R ++ L) (fun j => n + j)) :
    labelMap M hρ ≫ labelAppendSplit M (List.ofFn R) L =
      (coprod.inl : labelObj M L ⟶ labelObj M L ⨿ labelObj M (List.ofFn R)) := by
  apply Limits.Sigma.hom_ext
  intro i
  have hi : At L i (L.get i) := by simp [At]
  have he : labelInject M i hi =
      Limits.Sigma.ι (fun j : Fin L.length => M.obj (L.get j)) i := by
    unfold labelInject
    simp only [eqToHom_refl, Category.id_comp]
  change Limits.Sigma.ι (fun j : Fin L.length => M.obj (L.get j)) i ≫
      (labelMap M hρ ≫ labelAppendSplit M (List.ofFn R) L) =
      Limits.Sigma.ι (fun j : Fin L.length => M.obj (L.get j)) i ≫ coprod.inl
  rw [← he, labelInject_labelMap_assoc]
  exact labelAppendSplit_exit M R hi

set_option backward.isDefEq.respectTransparency false in
theorem cfgOutward_common (hu : IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (hr : Region.HasType Γ r L)
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) (List.ofFn R ++ L)) :
    ∃ (hs : Region.HasType Γ (.cfg (r.renameLabels (fun j => n + 1 + j)) (n + 1) blocks) L),
      ∃ f, RegionDenotes J M hr f ∧ RegionDenotes J M hs f := by
  let hρ : Ren L (List.ofFn R ++ L) (fun j => n + 1 + j) := fun _ _ hi => exitAt R hi
  obtain ⟨f, df⟩ := regionDenotes_exists J M hr
  let fb (i : Fin (n + 1)) := denoteRegion J M (hb i)
  obtain ⟨c, dc⟩ := collectiveDenotes_exists_succ J M n Γ R L fb
  have d := RegionDenotes.cfg (hr.renameLabels hρ) hb (df.renameLabels J M hρ)
    (fun i => denoteRegion_spec J M (hb i)) dc
  have hsplit : (f ≫ J.map (labelMap M hρ)) ≫ J.map (labelAppendSplit M (List.ofFn R) L) =
      f ≫ J.map (coprod.inl : labelObj M L ⟶ labelObj M L ⨿ labelObj M (List.ofFn R)) := by
    rw [Category.assoc, ← J.map_comp, outwardLabelMap]
  rw [hsplit, case_inl] at d
  simp only [Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical.bind, extend_snd J hu] at d
  exact ⟨_, f, df, d⟩

set_option backward.isDefEq.respectTransparency false in
theorem branchBind_common (hu : IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {Γ : VCtx τ} {L : LCtx τ} {ℓ : Nat} {a : Tm Φ} {A : τ}
    (hℓ : At L ℓ A) (ha : Tm.HasType Γ a A) :
    ∃ f, RegionDenotes J M (.br hℓ ha) f ∧
      RegionDenotes J M (.let₁ ha (.br hℓ (.var (i := 0) rfl))) f := by
  obtain ⟨f, df⟩ := denotes_exists J M ha
  have d := RegionDenotes.let₁ df (RegionDenotes.br (h := hℓ) (Denotes.var (i := 0) rfl))
  change RegionDenotes J M (.let₁ ha (.br hℓ (.var (i := 0) rfl)))
    (extend J f ≫ J.map (snd (ctxObj M Γ) (M.obj A)) ≫ J.map (labelInject M ℓ hℓ)) at d
  rw [← Category.assoc, extend_snd J hu] at d
  exact ⟨_, .br df, d⟩

set_option backward.isDefEq.respectTransparency false in
omit [SymmetricCategory V] [DistributiveTensor V] in
private theorem localLabelMap {n : Nat} (R : Fin n → τ) (L : LCtx τ)
    (hρ : Ren (List.ofFn R) (List.ofFn R ++ L) id) :
    labelMap M hρ ≫ labelAppendSplit M (List.ofFn R) L =
      (coprod.inr : labelObj M (List.ofFn R) ⟶ labelObj M L ⨿ labelObj M (List.ofFn R)) := by
  have hlocal {j : Nat} {A : τ} (hj : At (List.ofFn R) j A) :
      labelInject M j (hρ hj) ≫ labelAppendSplit M (List.ofFn R) L =
        labelInject M j hj ≫ coprod.inr := by
    have hlt := (List.getElem?_eq_some_iff.mp hj).1
    let i : Fin n := ⟨j, by simpa using hlt⟩
    have htype : A = R i := Option.some.inj (hj.symm.trans (ofFnAt R i))
    subst A
    exact labelAppendSplit_local M R i L
  apply Limits.Sigma.hom_ext
  intro j
  have he : labelInject M j (labelAt_get (List.ofFn R) j) =
      Limits.Sigma.ι (fun k : Fin (List.ofFn R).length => M.obj ((List.ofFn R).get k)) j := by
    unfold labelInject
    simp only [eqToHom_refl, Category.id_comp]
  rw [← he, labelInject_labelMap_assoc]
  exact hlocal (labelAt_get _ j)

set_option backward.isDefEq.respectTransparency false in
theorem cfgLink_common (hu : IsCentral (Functor.StrongPremonoidal.unitIso (J := J)).hom)
    {n : Nat} {Γ : VCtx τ} {L : LCtx τ} {r : Region Φ} {blocks : Fin (n + 1) → Region Φ}
    (R : Fin (n + 1) → τ) (hr : Region.HasType Γ r (List.ofFn R))
    (hb : ∀ i, Region.HasType (R i :: Γ) (blocks i) L)
    {f : J.obj (ctxObj M Γ) ⟶ J.obj (labelObj M (List.ofFn R))}
    (de : RegionDenotes J M hr f)
    {fb : ∀ i, J.obj (ctxObj M (R i :: Γ)) ⟶ J.obj (labelObj M L)}
    (db : ∀ i, RegionDenotes J M (hb i) (fb i))
    (g : J.obj (ctxObj M Γ ⊗ finiteLabelObj M R) ⟶ J.obj (labelObj M L))
    (hg : ∀ i, J.map (ctxObj M Γ ◁ finiteLabelInject M R i) ≫ g = fb i) :
    ∃ hs : Region.HasType Γ
      (.cfg r (n + 1) (fun i => (blocks i).renameLabels (fun j => n + 1 + j))) L,
      RegionDenotes J M hs (extend J f ≫ J.map (ctxObj M Γ ◁ labelObjToFinite M R) ≫ g) := by
  let hρ : Ren L (List.ofFn R ++ L) (fun j => n + 1 + j) := fun _ _ hi => exitAt R hi
  let hι : Ren (List.ofFn R) (List.ofFn R ++ L) id := by
    intro i A hi
    simpa only [id_eq, At, List.getElem?_append_left ((List.getElem?_eq_some_iff.mp hi).1)] using hi
  let split := labelAppendSplit M (List.ofFn R) L
  let E := ctxObj M Γ
  have transport {r' : Region Φ} (eq : r.renameLabels id = r') :
      ∃ ht : Region.HasType Γ r' (List.ofFn R ++ L),
        RegionDenotes J M ht (f ≫ J.map (labelMap M hι)) := by
    cases eq
    exact ⟨_, de.renameLabels J M hι⟩
  obtain ⟨he, de'⟩ := transport (Region.renameLabels_id r)
  let fb' (i : Fin (n + 1)) := fb i ≫ J.map (labelMap M hρ)
  obtain ⟨c, dc⟩ := collectiveDenotes_exists_succ J M n Γ R L fb'
  have den := RegionDenotes.cfg _ _ de' (fun i => (db i).renameLabels J M hρ) dc
  have hsplit : (f ≫ J.map (labelMap M hι)) ≫ J.map split =
      f ≫ J.map (coprod.inr : labelObj M (List.ofFn R) ⟶ labelObj M L ⨿ labelObj M (List.ofFn R)) := by
    dsimp only [split]
    rw [Category.assoc, ← J.map_comp, localLabelMap]
  have hg' : c ≫ J.map split =
      g ≫ J.map (coprod.inl : labelObj M L ⟶ labelObj M L ⨿ labelObj M (List.ofFn R)) := by
    apply collective_ext J M n Γ R
    intro i
    rw [← Category.assoc, dc.restrict i, ← Category.assoc, MonoidalCategory.id_tensorHom, hg i]
    simp only [fb', Category.assoc, ← J.map_comp, split, outwardLabelMap]
  have hbody : J.map (E ◁ labelObjToFinite M R) ≫ c ≫ J.map split =
      (J.map (E ◁ labelObjToFinite M R) ≫ g) ≫
        J.map (coprod.inl : labelObj M L ⟶ labelObj M L ⨿ labelObj M (List.ofFn R)) := by
    rw [hg', Category.assoc]
  simp only [MonoidalCategory.id_tensorHom] at den
  change RegionDenotes J M _ (caseWithContext J
    ((f ≫ J.map (labelMap M hι)) ≫ J.map split)
    (J.map (snd E (labelObj M L)))
    (contextualLoop J (J.map (E ◁ labelObjToFinite M R) ≫ c ≫ J.map split))) at den
  rw [hsplit, case_inr, hbody, contextualLoop_once J hu] at den
  exact ⟨_, den⟩

end Cfg

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite
