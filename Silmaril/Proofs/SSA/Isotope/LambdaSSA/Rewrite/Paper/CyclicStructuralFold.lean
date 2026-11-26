module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.HiddenBit.Unit.Thms

/-! # Fold a duplicated Unit in otherwise arbitrary guarded feedback -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CyclicStructuralFold

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.Extension.Singleton.ValueCoproducts (exactCopair)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic
open Paper.WithCaseReturns.StructuralValues.HiddenBit
  (binary_fold_of_closed_mode_of_seed binary_fold_iff_mixed_of_seed
   binary_fold_of_right_switch_and_double_of_seed unit_alternate_power_of_seed unit_fold_of_shared_choice)

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (S : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)

local notation "Q" => TypeCategory S
local notation "Obj" => ofType S
local notation "I" => iterateChosen S
local notation "U" => (Silmaril.unit : τ)
local infixr:65 " ⊕ₜ " => Silmaril.coprod

variable (R : τ)

local notation "Dom" => Obj (U ⊕ₜ (U ⊕ₜ R))
local notation "Cod" => Obj (U ⊕ₜ R)
local notation "C" => Obj R
local notation "X" => Obj U
local notation "F" => foldState S R
local notation "s" => sourceIso S R
local notation "t" => targetIso S R
local notation "k" => coprod.desc (𝟙 X) (𝟙 X)
local notation "p" => coprod.map (𝟙 C) k

private abbrev extra : X ⟶ Dom := (sumCofan S U (U ⊕ₜ R)).inl
private abbrev original : Cod ⟶ Dom := (sumCofan S U (U ⊕ₜ R)).inr
private abbrev unitTag : X ⟶ Cod := (sumCofan S U R).inl
private abbrev retainedTag : C ⟶ Cod := (sumCofan S U R).inr

private theorem fold_inl : extra S R ≫ F = unitTag S R :=
  (sumCofanIsColimit S U (U ⊕ₜ R)).fac (BinaryCofan.mk (unitTag S R) (𝟙 Cod)) ⟨WalkingPair.left⟩

private theorem fold_inr : original S R ≫ F = 𝟙 Cod :=
  (sumCofanIsColimit S U (U ⊕ₜ R)).fac (BinaryCofan.mk (unitTag S R) (𝟙 Cod)) ⟨WalkingPair.right⟩

set_option backward.isDefEq.respectTransparency false in
theorem fold_coordinates : (s).hom ≫ p = F ≫ (t).hom := by
  have el : extra S R ≫ (sumIso S U (U ⊕ₜ R)).hom = coprod.inl :=
    sumCofan_inl_sumIso_hom S U (U ⊕ₜ R)
  have er : original S R ≫ (sumIso S U (U ⊕ₜ R)).hom = coprod.inr :=
    sumCofan_inr_sumIso_hom S U (U ⊕ₜ R)
  have ul : unitTag S R ≫ (sumIso S U R).hom = coprod.inl := sumCofan_inl_sumIso_hom S U R
  have ur : retainedTag S R ≫ (sumIso S U R).hom = coprod.inr := sumCofan_inr_sumIso_hom S U R
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit S U (U ⊕ₜ R))
  · change extra S R ≫ (s).hom ≫ p = extra S R ≫ F ≫ (t).hom
    simp [sourceIso, targetIso, rotate, swap, Category.assoc, reassoc_of% el,
      reassoc_of% ul, reassoc_of% fold_inl S R]
  · change original S R ≫ (s).hom ≫ p = original S R ≫ F ≫ (t).hom
    rw [reassoc_of% fold_inr S R]
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit S U R)
    · change unitTag S R ≫ (original S R ≫ (s).hom ≫ p) = unitTag S R ≫ (t).hom
      simp [sourceIso, targetIso, rotate, swap, Category.assoc, reassoc_of% er, reassoc_of% ul]
    · change retainedTag S R ≫ (original S R ≫ (s).hom ≫ p) = retainedTag S R ≫ (t).hom
      simp [sourceIso, targetIso, rotate, swap, Category.assoc, reassoc_of% er, reassoc_of% ur]

theorem iterate_realize {A D B Z : Q} (iso : Z ≅ A ⨿ D) (d : A ⨿ D ⟶ (B ⨿ A) ⨿ D) :
    I (realize S iso d) = iso.hom ≫ I (d ≫ (coprod.associator B A D).hom) := by
  apply uniformity_of_iso
  simp only [realize, Category.assoc, coprod.map_map, Iso.inv_hom_id, coprod.map_id_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem fold_square_iff {B : Q}
    (d : C ⨿ (X ⨿ X) ⟶ (B ⨿ C) ⨿ (X ⨿ X))
    (e : C ⨿ X ⟶ (B ⨿ C) ⨿ X) :
    realize S (s) d ≫ coprod.map (𝟙 B) F = F ≫ realize S (t) e ↔
      d ≫ coprod.map (𝟙 (B ⨿ C)) k = p ≫ e := by
  let l := d ≫ (coprod.associator B C (X ⨿ X)).hom
  let r := e ≫ (coprod.associator B C X).hom
  let out := (coprod.mapIso (Iso.refl B) (t).symm).hom
  have inverse : (s).inv ≫ F = p ≫ (t).inv := by
    have eq := congrArg (fun f => (s).inv ≫ f ≫ (t).inv) (fold_coordinates S R)
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using eq.symm
  have hl : realize S (s) d ≫ coprod.map (𝟙 B) F =
      (s).hom ≫ (l ≫ coprod.map (𝟙 B) p) ≫ out := by
    simp only [realize, l, out, coprod.mapIso_hom, Iso.refl_hom, Iso.symm_hom,
      Category.assoc, coprod.map_map, Category.id_comp, inverse]
  have hr : F ≫ realize S (t) e = (s).hom ≫ (p ≫ r) ≫ out := by
    have coords := fold_coordinates S R
    simp only [realize, r, out, coprod.mapIso_hom, Iso.refl_hom, Iso.symm_hom, Category.assoc]
    rw [← Category.assoc F, ← coords, Category.assoc]
  rw [hl, hr, cancel_epi, cancel_mono]
  exact iterateChosen_block_square_iff S k d e

set_option hygiene false in
set_option quotPrecheck false in
local notation "q" => (coprod.inr ≫ d)
set_option hygiene false in
set_option quotPrecheck false in
local notation "g" => (coprod.inr ≫ e)
set_option hygiene false in
set_option quotPrecheck false in
local notation "squareOnBlocks" =>
  (d ≫ coprod.map (𝟙 (B ⨿ C)) k = p ≫ e)
set_option hygiene false in
set_option quotPrecheck false in
local notation "squareOnStates" =>
  (realize S (s) d ≫ coprod.map (𝟙 B) F = F ≫ realize S (t) e)
set_option hygiene false in
set_option quotPrecheck false in
local notation "foldsIteration" =>
  (I (realize S (s) d) = F ≫ I (realize S (t) e))

private theorem inner_square {B : Q}
    {d : C ⨿ (X ⨿ X) ⟶ (B ⨿ C) ⨿ (X ⨿ X)}
    {e : C ⨿ X ⟶ (B ⨿ C) ⨿ X} (rows : squareOnBlocks) :
    q ≫ coprod.map (𝟙 (B ⨿ C)) k = k ≫ g := by
  rw [Category.assoc, rows, coprod.inr_map_assoc]

private theorem of_inner {B : Q}
    {d : C ⨿ (X ⨿ X) ⟶ (B ⨿ C) ⨿ (X ⨿ X)}
    {e : C ⨿ X ⟶ (B ⨿ C) ⨿ X} (rows : squareOnBlocks)
    (inner : I q = k ≫ I g) : foldsIteration := by
  rw [iterate_realize, iterate_realize, iterateChosen_of_right_block S k d e rows inner,
    ← Category.assoc, fold_coordinates, Category.assoc]

theorem uniformity_of_right_self {B : Q}
    (d : C ⨿ (X ⨿ X) ⟶ (B ⨿ C) ⨿ (X ⨿ X))
    (e : C ⨿ X ⟶ (B ⨿ C) ⨿ X) (square : squareOnStates)
    (self : coprod.inr ≫ q = g ≫ coprod.map (𝟙 (B ⨿ C)) (coprod.inr : X ⟶ X ⨿ X)) :
    foldsIteration := by
  have rows := (fold_square_iff S R d e).1 square
  exact of_inner S R rows
    (binary_fold_of_closed_mode_of_seed S q g (inner_square S R rows) (.inr self))

theorem uniformity_of_mixed_identity {B : Q}
    (d : C ⨿ (X ⨿ X) ⟶ (B ⨿ C) ⨿ (X ⨿ X))
    (e : C ⨿ X ⟶ (B ⨿ C) ⨿ X) (square : squareOnStates)
    (mixed :
      let a := q ≫ (coprod.associator (B ⨿ C) X X).inv
      I ((coprod.inl ≫ a) ≫ coprod.desc (𝟙 ((B ⨿ C) ⨿ X)) (I (coprod.inr ≫ a))) = I g) :
    foldsIteration := by
  have rows := (fold_square_iff S R d e).1 square
  let i := coprod.associator (B ⨿ C) X X
  have flat : i.inv ≫ coprod.desc (𝟙 ((B ⨿ C) ⨿ X)) (coprod.inr : X ⟶ (B ⨿ C) ⨿ X) =
      coprod.map (𝟙 (B ⨿ C)) k := by
    apply (cancel_epi i.hom).1
    rw [Iso.hom_inv_id_assoc]
    apply coprod.hom_ext
    · apply coprod.hom_ext <;> simp [i, coprod.associator]
    · simp [i, coprod.associator]
  have right : (coprod.inr ≫ (q ≫ i.inv)) ≫
      coprod.desc (𝟙 ((B ⨿ C) ⨿ X)) (coprod.inr : X ⟶ (B ⨿ C) ⨿ X) = g := by
    rw [Category.assoc, Category.assoc, flat, inner_square S R rows,
      coprod.inr_desc_assoc, Category.id_comp]
  have inner := (binary_fold_iff_mixed_of_seed S (q ≫ i.inv) g right).2 mixed
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id] at inner
  exact of_inner S R rows inner

theorem uniformity_of_right_switch
    (includeUnit : ∀ {Γ : VCtx τ} {left right : Region Φ} {L : LCtx τ},
      Paper.WithUnitEta.Step Γ left right L → S Γ left right L)
    {B : Q} (d : C ⨿ (X ⨿ X) ⟶ (B ⨿ C) ⨿ (X ⨿ X))
    (e : C ⨿ X ⟶ (B ⨿ C) ⨿ X)
    (square : realize S (s) d ≫ coprod.map (𝟙 B) F = F ≫ realize S (t) e)
    (switch : coprod.inr ≫ (coprod.inr ≫ d) =
      (coprod.inr ≫ e) ≫ coprod.map (𝟙 (B ⨿ C)) (coprod.inl : X ⟶ X ⨿ X)) :
    I (realize S (s) d) = F ≫ I (realize S (t) e) := by
  have rows := (fold_square_iff S R d e).1 square
  exact of_inner S R rows
    (binary_fold_of_right_switch_and_double_of_seed S q g (inner_square S R rows) switch
      (unit_alternate_power_of_seed S includeUnit _))

theorem uniformity_of_shared_choice
    (includeUnit : ∀ {Γ : VCtx τ} {left right : Region Φ} {L : LCtx τ},
      Paper.WithUnitEta.Step Γ left right L → S Γ left right L)
    {B : Q} (d : C ⨿ (X ⨿ X) ⟶ (B ⨿ C) ⨿ (X ⨿ X))
    (e : C ⨿ X ⟶ (B ⨿ C) ⨿ X) (square : squareOnStates)
    (decision : X ⟶ (B ⨿ C) ⨿ (X ⨿ X))
    (route : q = coprod.desc decision
      (decision ≫ coprod.map (𝟙 (B ⨿ C)) (coprod.desc coprod.inr coprod.inl))) :
    foldsIteration := by
  have rows := (fold_square_iff S R d e).1 square
  have target : decision ≫ coprod.map (𝟙 (B ⨿ C)) k = g := by
    have eq := congrArg ((coprod.inl : X ⟶ X ⨿ X) ≫ ·) (inner_square S R rows)
    simpa only [← Category.assoc, route, coprod.inl_desc, Category.id_comp] using eq
  apply of_inner S R rows
  rw [route, ← target]
  exact unit_fold_of_shared_choice S includeUnit decision

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CyclicStructuralFold
