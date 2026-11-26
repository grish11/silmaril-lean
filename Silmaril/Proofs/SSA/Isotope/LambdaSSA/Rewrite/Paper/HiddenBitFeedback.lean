module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.HiddenBit.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.Thms

/-! # Eliminate one mode of a hidden-bit feedback step -/

public section

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open scoped MonoidalCategory


namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback

namespace TwoMode

universe u v
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  (Seed : VCtx τ → Region Φ → Region Φ → LCtx τ → Prop)
local notation "Q" => TypeCategory Seed
local notation "I" => iterateChosen Seed

set_option hygiene false in
set_option quotPrecheck false in
local notation "S" => A ⨿ A
set_option hygiene false in
set_option quotPrecheck false in
local notation "l" => (coprod.inl : A ⟶ A ⨿ A)
set_option hygiene false in
set_option quotPrecheck false in
local notation "r" => (coprod.inr : A ⟶ A ⨿ A)
set_option hygiene false in
set_option quotPrecheck false in
local notation "fold" => coprod.desc (𝟙 A) (𝟙 A)

set_option hygiene false in
set_option quotPrecheck false in
local notation "assocSum" => (coprod.associator B A A)
set_option hygiene false in
set_option quotPrecheck false in
local notation "flatten" => coprod.desc (𝟙 (B ⨿ A)) (coprod.inr : A ⟶ B ⨿ A)

private theorem assoc_fold (A B : Q) :
    (assocSum).hom ≫ coprod.map (𝟙 B) fold = flatten := by
  apply coprod.hom_ext
  · simp [coprod.associator]
  · simp [coprod.associator]

/-- The left row of full feedback is computed after eliminating the right recursive mode. -/
theorem left_iteration {A B : Q} (d : S ⟶ (B ⨿ A) ⨿ A) :
    l ≫ I (d ≫ (assocSum).hom) =
      I ((l ≫ d) ≫ coprod.desc (𝟙 (B ⨿ A)) (I (r ≫ d))) := by
  rw [iterateChosen_rows Seed d, coprod.inl_desc]

/-- The projected square is equivalent to flattening each row to the same visible step. -/
theorem rows_iff {A B : Q} (d : S ⟶ (B ⨿ A) ⨿ A) (g : A ⟶ B ⨿ A) :
    (d ≫ (assocSum).hom) ≫ coprod.map (𝟙 B) fold = fold ≫ g ↔
      (l ≫ d) ≫ flatten = g ∧ (r ≫ d) ≫ flatten = g := by
  rw [Category.assoc, assoc_fold]
  constructor
  · intro h
    constructor
    · rw [Category.assoc, h, coprod.inl_desc_assoc, Category.id_comp]
    · rw [Category.assoc, h, coprod.inr_desc_assoc, Category.id_comp]
  · rintro ⟨hl, hr⟩
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, Category.id_comp, ← Category.assoc, hl]
    · rw [coprod.inr_desc_assoc, Category.id_comp, ← Category.assoc, hr]

/-- With both projected row equations, only the mixed left-row iteration law remains. -/
theorem iterate_iff_mixed {A B : Q} (d : S ⟶ (B ⨿ A) ⨿ A) (g : A ⟶ B ⨿ A)
    (right : (r ≫ d) ≫ flatten = g) :
    I (d ≫ (assocSum).hom) = fold ≫ I g ↔
      I ((l ≫ d) ≫ coprod.desc (𝟙 (B ⨿ A)) (I (r ≫ d))) = I g := by
  constructor
  · intro h
    rw [← left_iteration, h, coprod.inl_desc_assoc, Category.id_comp]
  · intro mixed
    have hg : I (I (r ≫ d)) = I g := by rw [iterateChosen_codiagonal, right]
    rw [iterateChosen_rows Seed d, mixed]
    apply coprod.hom_ext
    · simp only [coprod.inl_desc, coprod.inl_desc_assoc, Category.id_comp]
    · simp only [coprod.inr_desc, coprod.inr_desc_assoc, Category.id_comp]
      rw [← hg, ← iterateChosen_fixpoint]


/-- Express a step with a two-mode state as two visible feedback rows. -/
noncomputable abbrev rowsOf {A X B : Q} (e : S ≅ X) (f : X ⟶ B ⨿ X) :
    S ⟶ (B ⨿ A) ⨿ A :=
  e.hom ≫ f ≫ coprod.map (𝟙 B) e.inv ≫ (assocSum).inv

private theorem rowsOf_assoc {A X B : Q} (e : S ≅ X) (f : X ⟶ B ⨿ X) :
    rowsOf Seed e f ≫ (assocSum).hom = e.hom ≫ f ≫ coprod.map (𝟙 B) e.inv := by
  simp only [rowsOf, Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem square_iff_rowsOf {A X B : Q} (e : S ≅ X) (p : X ⟶ A) (fold_eq : e.hom ≫ p = fold)
    (f : X ⟶ B ⨿ X) (g : A ⟶ B ⨿ A) :
    f ≫ coprod.map (𝟙 B) p = p ≫ g ↔
      (l ≫ rowsOf Seed e f) ≫ flatten = g ∧ (r ≫ rowsOf Seed e f) ≫ flatten = g := by
  rw [← rows_iff Seed, rowsOf_assoc]
  have inv_fold : e.inv ≫ fold = p := by rw [← fold_eq, Iso.inv_hom_id_assoc]
  simp only [Category.assoc, coprod.map_map, Category.id_comp, inv_fold]
  rw [← fold_eq, Category.assoc, cancel_epi]

theorem uniformity_iff_mixed_rowsOf {A X B : Q} (e : S ≅ X) (p : X ⟶ A)
    (fold_eq : e.hom ≫ p = fold) (f : X ⟶ B ⨿ X) (g : A ⟶ B ⨿ A)
    (square : f ≫ coprod.map (𝟙 B) p = p ≫ g) :
    I f = p ≫ I g ↔
      I ((l ≫ rowsOf Seed e f) ≫ coprod.desc (𝟙 (B ⨿ A)) (I (r ≫ rowsOf Seed e f))) = I g := by
  rw [← iterate_iff_mixed Seed _ g ((square_iff_rowsOf Seed e p fold_eq f g).1 square).2,
    rowsOf_assoc]
  have square_iso : (e.hom ≫ f ≫ coprod.map (𝟙 B) e.inv) ≫ coprod.map (𝟙 B) e.hom = e.hom ≫ f := by
    simp only [Category.assoc, coprod.map_map, Iso.inv_hom_id, coprod.map_id_id,
      Category.comp_id]
  rw [uniformity_of_iso Seed e _ _ square_iso, ← fold_eq, Category.assoc, cancel_epi]

noncomputable def alternateRows {A B : Q} (g : A ⟶ B ⨿ A) : S ⟶ (B ⨿ A) ⨿ A :=
  coprod.desc (g ≫ coprod.map (coprod.inl : B ⟶ B ⨿ A) (𝟙 A))
    (g ≫ coprod.inl)

theorem alternate_rows {A B : Q} (g : A ⟶ B ⨿ A) :
    (l ≫ alternateRows Seed g) ≫ flatten = g ∧ (r ≫ alternateRows Seed g) ≫ flatten = g := by
  constructor
  · simp only [alternateRows, coprod.inl_desc, Category.assoc, coprod.map_desc,
      Category.comp_id, Category.id_comp, coprod.desc_inl_inr]
  · simp only [alternateRows, coprod.inr_desc, Category.assoc, coprod.inl_desc, Category.comp_id]

theorem alternate_row_routes {A B : Q} (g : A ⟶ B ⨿ A) :
    l ≫ (alternateRows Seed g ≫ (assocSum).hom) = g ≫ coprod.map (𝟙 B) r ∧
    r ≫ (alternateRows Seed g ≫ (assocSum).hom) = g ≫ coprod.map (𝟙 B) l := by
  have hl : coprod.map (coprod.inl : B ⟶ B ⨿ A) (𝟙 A) ≫ (assocSum).hom =
      coprod.map (𝟙 B) r := by
    apply coprod.hom_ext <;> simp [coprod.associator]
  have hr : coprod.inl ≫ (assocSum).hom = coprod.map (𝟙 B) l := by
    apply coprod.hom_ext <;> simp [coprod.associator]
  constructor
  · rw [alternateRows, coprod.inl_desc_assoc, Category.assoc, hl]
  · rw [alternateRows, coprod.inr_desc_assoc, Category.assoc, hr]

theorem alternate_uniform_iff {A B : Q} (g : A ⟶ B ⨿ A) :
    I (alternateRows Seed g ≫ (assocSum).hom) = fold ≫ I g ↔
      I (g ≫ coprod.desc coprod.inl g) = I g := by
  rw [iterate_iff_mixed Seed _ g (alternate_rows Seed g).2]
  have right : I (r ≫ alternateRows Seed g) = g := by
    rw [alternateRows, coprod.inr_desc]
    conv_lhs => rw [iterateChosen_fixpoint Seed (g ≫ coprod.inl)]
    rw [Category.assoc, coprod.inl_desc, Category.comp_id]
  rw [right, alternateRows, coprod.inl_desc, Category.assoc, coprod.map_desc,
    Category.comp_id, Category.id_comp]

private theorem binary_fold_of_left_closed {A B : Q} (f : A ⨿ A ⟶ B ⨿ (A ⨿ A)) (g : A ⟶ B ⨿ A)
    (square : f ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 A) (𝟙 A)) =
      coprod.desc (𝟙 A) (𝟙 A) ≫ g)
    (closed : coprod.inl ≫ f = g ≫ coprod.map (𝟙 B) (coprod.inl : A ⟶ A ⨿ A)) :
    I f = coprod.desc (𝟙 A) (𝟙 A) ≫ I g := by
  let e := coprod.associator B A A
  let d := f ≫ e.inv
  have d_eq : d ≫ e.hom = f := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hd : (coprod.inr ≫ d) ≫ coprod.desc (𝟙 (B ⨿ A)) coprod.inr = g :=
    ((rows_iff Seed d g).1 (d_eq.symm ▸ square)).2
  have route : coprod.map (𝟙 B) (coprod.inl : A ⟶ A ⨿ A) ≫ e.inv = coprod.inl := by
    apply (cancel_mono e.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply coprod.hom_ext <;> simp [e, coprod.associator]
  have leftRow : coprod.inl ≫ d = g ≫ coprod.inl := by
    dsimp only [d]
    rw [← Category.assoc, closed, Category.assoc, route]
  rw [← d_eq, iterate_iff_mixed Seed d g hd, leftRow,
    Category.assoc, coprod.inl_desc, Category.comp_id]

private noncomputable def swapModes (A : Q) : A ⨿ A ≅ A ⨿ A where
  hom := coprod.desc coprod.inr coprod.inl
  inv := coprod.desc coprod.inr coprod.inl
  hom_inv_id := coprod.hom_ext (by simp) (by simp)
  inv_hom_id := coprod.hom_ext (by simp) (by simp)

private theorem binary_fold_of_right_closed {A B : Q} (f : A ⨿ A ⟶ B ⨿ (A ⨿ A)) (g : A ⟶ B ⨿ A)
    (square : f ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 A) (𝟙 A)) =
      coprod.desc (𝟙 A) (𝟙 A) ≫ g)
    (closed : coprod.inr ≫ f = g ≫ coprod.map (𝟙 B) (coprod.inr : A ⟶ A ⨿ A)) :
    I f = coprod.desc (𝟙 A) (𝟙 A) ≫ I g := by
  let e := swapModes Seed A
  let k : A ⨿ A ⟶ A := coprod.desc (𝟙 A) (𝟙 A)
  let f' := e.hom ≫ f ≫ coprod.map (𝟙 B) e.inv
  have swapFold : e.hom ≫ k = k := coprod.hom_ext (by simp [e, swapModes, k]) (by simp [e, swapModes, k])
  have swapFoldInv : e.inv ≫ k = k := swapFold
  have square' : f' ≫ coprod.map (𝟙 B) k = k ≫ g := by
    dsimp only [f']
    rw [Category.assoc, Category.assoc, coprod.map_map, Category.id_comp, swapFoldInv,
      square, ← Category.assoc, swapFold]
  have closed' : coprod.inl ≫ f' = g ≫ coprod.map (𝟙 B) (coprod.inl : A ⟶ A ⨿ A) := by
    dsimp only [f']
    rw [← Category.assoc, show coprod.inl ≫ e.hom = coprod.inr from coprod.inl_desc _ _,
      ← Category.assoc, closed, Category.assoc, coprod.map_map, Category.id_comp,
      show coprod.inr ≫ e.inv = coprod.inl from coprod.inr_desc _ _]
  have comm : f' ≫ coprod.map (𝟙 B) e.hom = e.hom ≫ f := by
    simp only [f', Category.assoc, coprod.map_map, Iso.inv_hom_id,
      coprod.map_id_id, Category.comp_id]
  have eq := (uniformity_of_iso Seed e f' f comm).symm.trans
    (binary_fold_of_left_closed Seed f' g square' closed')
  apply (cancel_epi e.hom).1
  rwa [← Category.assoc, swapFold]

theorem binary_fold_of_closed_mode {A B : Q}
    (f : A ⨿ A ⟶ B ⨿ (A ⨿ A)) (g : A ⟶ B ⨿ A)
    (square : f ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 A) (𝟙 A)) =
      coprod.desc (𝟙 A) (𝟙 A) ≫ g)
    (closed :
      coprod.inl ≫ f = g ≫ coprod.map (𝟙 B) (coprod.inl : A ⟶ A ⨿ A) ∨
      coprod.inr ≫ f = g ≫ coprod.map (𝟙 B) (coprod.inr : A ⟶ A ⨿ A)) :
    I f = coprod.desc (𝟙 A) (𝟙 A) ≫ I g :=
  closed.elim (binary_fold_of_left_closed Seed f g square)
    (binary_fold_of_right_closed Seed f g square)

/-- Codiagonal converts doubling at the enlarged outward type into the
selective double-step identity. No uniformity on the fold is used here. -/
private theorem selective_of_double_at_enlarged_exit {A B : Q}
    (p : A ⟶ (B ⨿ A) ⨿ A)
    (double : I (p ≫ coprod.desc coprod.inl p) = I p) :
    I (p ≫ coprod.desc (𝟙 (B ⨿ A)) (p ≫ flatten)) = I (p ≫ flatten) := by
  have h := congrArg (fun t : A ⟶ B ⨿ A => I t) double
  rw [iterateChosen_codiagonal, iterateChosen_codiagonal] at h
  rw [Category.assoc, coprod.desc_comp] at h
  have route : (coprod.inl : B ⨿ A ⟶ (B ⨿ A) ⨿ A) ≫ flatten = 𝟙 (B ⨿ A) :=
    coprod.inl_desc _ _
  rw [route] at h
  exact h

theorem binary_fold_of_right_switch_and_double {A B : Q}
    (f : A ⨿ A ⟶ B ⨿ (A ⨿ A)) (g : A ⟶ B ⨿ A)
    (square : f ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 A) (𝟙 A)) =
      coprod.desc (𝟙 A) (𝟙 A) ≫ g)
    (switch : coprod.inr ≫ f = g ≫ coprod.map (𝟙 B) (coprod.inl : A ⟶ A ⨿ A))
    (double :
      let p := (coprod.inl ≫ f) ≫ (coprod.associator B A A).inv
      I (p ≫ coprod.desc coprod.inl p) = I p) :
    I f = coprod.desc (𝟙 A) (𝟙 A) ≫ I g := by
  let e := coprod.associator B A A
  let d := f ≫ e.inv
  let p := coprod.inl ≫ d
  have d_eq : d ≫ e.hom = f := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  obtain ⟨flat_p, flat_q⟩ := (rows_iff Seed d g).1 (d_eq.symm ▸ square)
  have route : coprod.map (𝟙 B) (coprod.inl : A ⟶ A ⨿ A) ≫ e.inv = coprod.inl := by
    apply (cancel_mono e.hom).1
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply coprod.hom_ext <;> simp [e, coprod.associator]
  have rightRow : coprod.inr ≫ d = g ≫ coprod.inl := by
    dsimp only [d]
    rw [← Category.assoc, switch, Category.assoc, route]
  have inject : I (g ≫ (coprod.inl : B ⨿ A ⟶ (B ⨿ A) ⨿ A)) = g := by
    rw [iterateChosen_fixpoint Seed (g ≫ coprod.inl), Category.assoc, coprod.inl_desc, Category.comp_id]
  have pow : I (p ≫ coprod.desc coprod.inl p) = I p := by
    simpa only [p, d, e, Category.assoc] using double
  have eq := selective_of_double_at_enlarged_exit Seed p pow
  change p ≫ flatten = g at flat_p
  rw [flat_p] at eq
  rw [← d_eq, iterate_iff_mixed Seed _ _ flat_q, rightRow, inject]
  exact eq

end TwoMode

open Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.StructuralValues.HiddenBit
open Paper.WithCaseReturns.StructuralValues
open Paper.RetainedCase.Chosen (projectedChosenDistributor projectedChosenDistributor_hom)
open Paper.Extension.Singleton.StructuralValues (HomProperty sum_inl_mem sum_inr_mem fst_mem)

universe u v w
variable {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ] {ε : Type w} [HasEff Φ ε] (pe : ε)
local notation "Seed" => Paper.WithCaseReturns.JoinedStep (τ := τ) (Φ := Φ) pe
local notation "Q" => TypeCategory Seed
local notation "V" => ValueCategory (τ := τ) (Φ := Φ) pe
local notation "J" => inclusion (τ := τ) (Φ := Φ) pe
local notation "U" => (Silmaril.unit : τ)
local notation "Bit" => Silmaril.coprod U U
local notation "Obj" => ofType Seed

attribute [local instance] valueCartesian computationPremonoidal computationSymmetric computationDistributive

private abbrev unitIso (A : τ) : Obj (product A U) ≅ Obj A :=
  rightUnitIsoOfEta Seed (unit_eta_of_include Seed (Paper.WithCaseReturns.includeUnit pe)) (Obj A)

set_option backward.isDefEq.respectTransparency false in
private theorem modes_inl (A : τ) :
    coprod.inl ≫ (modes pe A).hom =
      (unitIso pe A).inv ≫ whiskerLeft Seed (Obj A) (sumCofan Seed U U).inl := by
  let F := whiskerLeftFunctor Seed (Obj A)
  change coprod.inl ≫ coprod.map (unitIso pe A).inv (unitIso pe A).inv ≫
    (projectedChosenDistributor Seed A U U).hom ≫ F.map (sumIso Seed U U).inv = _
  have cmp :
      (coprod.inl : Obj (product A U) ⟶ Obj (product A U) ⨿ Obj (product A U)) ≫
        (projectedChosenDistributor Seed A U U).hom = F.map (coprod.inl : Obj U ⟶ Obj U ⨿ Obj U) := by
    rw [projectedChosenDistributor_hom]
    exact inl_coprodComparison F (Obj U) (Obj U)
  rw [coprod.inl_map_assoc, ← Category.assoc (coprod.inl : Obj (product A U) ⟶ _), cmp]
  change (unitIso pe A).inv ≫ F.map coprod.inl ≫ F.map (sumIso Seed U U).inv =
    (unitIso pe A).inv ≫ F.map (sumCofan Seed U U).inl
  have convert : (coprod.inl : Obj U ⟶ Obj U ⨿ Obj U) ≫ (sumIso Seed U U).inv =
      (sumCofan Seed U U).inl := by
    rw [← sumCofan_inl_sumIso_hom Seed U U, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← F.map_comp]
  exact congrArg (fun x : Obj U ⟶ Obj Bit => (unitIso pe A).inv ≫ F.map x) convert

set_option backward.isDefEq.respectTransparency false in
private theorem modes_inr (A : τ) :
    coprod.inr ≫ (modes pe A).hom =
      (unitIso pe A).inv ≫ whiskerLeft Seed (Obj A) (sumCofan Seed U U).inr := by
  let F := whiskerLeftFunctor Seed (Obj A)
  change coprod.inr ≫ coprod.map (unitIso pe A).inv (unitIso pe A).inv ≫
    (projectedChosenDistributor Seed A U U).hom ≫ F.map (sumIso Seed U U).inv = _
  have cmp :
      (coprod.inr : Obj (product A U) ⟶ Obj (product A U) ⨿ Obj (product A U)) ≫
        (projectedChosenDistributor Seed A U U).hom = F.map (coprod.inr : Obj U ⟶ Obj U ⨿ Obj U) := by
    rw [projectedChosenDistributor_hom]
    exact inr_coprodComparison F (Obj U) (Obj U)
  rw [coprod.inr_map_assoc, ← Category.assoc (coprod.inr : Obj (product A U) ⟶ _), cmp]
  change (unitIso pe A).inv ≫ F.map coprod.inr ≫ F.map (sumIso Seed U U).inv =
    (unitIso pe A).inv ≫ F.map (sumCofan Seed U U).inr
  have convert : (coprod.inr : Obj U ⟶ Obj U ⨿ Obj U) ≫ (sumIso Seed U U).inv =
      (sumCofan Seed U U).inr := by
    rw [← sumCofan_inr_sumIso_hom Seed U U, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← F.map_comp]
  exact congrArg (fun x : Obj U ⟶ Obj Bit => (unitIso pe A).inv ≫ F.map x) convert

private theorem whisker_fst (A : τ) {D E : τ} {h : Obj D ⟶ Obj E} (hh : HomProperty Seed h) :
    whiskerLeft Seed (Obj A) h ≫ productFst Seed A E = productFst Seed A D := by
  let f : (⟨Obj D⟩ : V) ⟶ ⟨Obj E⟩ := ⟨h, hh⟩
  have e := congrArg (J).map (CartesianMonoidalCategory.whiskerLeft_fst (⟨Obj A⟩ : V) f)
  rw [(J).map_comp, Paper.Extension.Singleton.StructuralValues.map_whiskerLeft Seed
    (Paper.WithCaseReturns.includeUnit pe) A f] at e
  exact e

set_option backward.isDefEq.respectTransparency false in
theorem modes_fst (A : τ) :
    (modes pe A).hom ≫ productFst Seed A Bit = coprod.desc (𝟙 (Obj A)) (𝟙 (Obj A)) := by
  apply coprod.hom_ext
  · rw [← Category.assoc, modes_inl, Category.assoc, whisker_fst pe A (sum_inl_mem Seed U U),
      coprod.inl_desc]
    exact (unitIso pe A).inv_hom_id
  · rw [← Category.assoc, modes_inr, Category.assoc, whisker_fst pe A (sum_inr_mem Seed U U),
      coprod.inr_desc]
    exact (unitIso pe A).inv_hom_id

local notation "I" => iterateChosen Seed

theorem leftMode_fst (A : τ) :
    leftMode pe A ≫ productFst Seed A Bit = 𝟙 _ := by
  rw [leftMode, Category.assoc, modes_fst, coprod.inl_desc]

theorem projection_square_rows (A : τ) {B : Q}
    (f : Obj (product A Bit) ⟶ B ⨿ Obj (product A Bit)) (g : Obj A ⟶ B ⨿ Obj A) :
    let d := rows pe A f
    let flat := coprod.desc (𝟙 (B ⨿ Obj A)) coprod.inr
    f ≫ coprod.map (𝟙 B) (productFst Seed A Bit) = productFst Seed A Bit ≫ g ↔
      (coprod.inl ≫ d) ≫ flat = g ∧ (coprod.inr ≫ d) ≫ flat = g :=
  TwoMode.square_iff_rowsOf Seed (modes pe A) _ (modes_fst pe A) f g

/-- With the actual projection square, resetting to the left mode is exactly the mixed row equation. -/
theorem hidden_bit_reset_iff_mixed (A : τ) {B : Q}
    (f : Obj (product A Bit) ⟶ B ⨿ Obj (product A Bit)) (g : Obj A ⟶ B ⨿ Obj A)
    (square : f ≫ coprod.map (𝟙 B) (productFst Seed A Bit) = productFst Seed A Bit ≫ g) :
    let d := rows pe A f
    I f = I (f ≫ coprod.map (𝟙 B) (productFst Seed A Bit ≫ leftMode pe A)) ↔
      I ((coprod.inl ≫ d) ≫ coprod.desc (𝟙 (B ⨿ Obj A)) (I (coprod.inr ≫ d))) = I g :=
  (uniformity_iff_reset Seed _ (leftMode pe A) (leftMode_fst pe A) f g square).symm.trans
    (TwoMode.uniformity_iff_mixed_rowsOf Seed (modes pe A) _ (modes_fst pe A) f g square)

private theorem alternating_eq {A B : Q} (g : A ⟶ B ⨿ A) :
    TwoMode.alternateRows Seed g ≫ (coprod.associator B A A).hom = alternatingStep pe g :=
  coprod.hom_ext ((TwoMode.alternate_row_routes Seed g).1.trans (coprod.inl_desc _ _).symm)
    ((TwoMode.alternate_row_routes Seed g).2.trans (coprod.inr_desc _ _).symm)

theorem alternating_fold_square {A B : Q} (g : A ⟶ B ⨿ A) :
    alternatingStep pe g ≫ coprod.map (𝟙 B) (coprod.desc (𝟙 A) (𝟙 A)) =
      coprod.desc (𝟙 A) (𝟙 A) ≫ g := by
  rw [← alternating_eq]
  exact (TwoMode.rows_iff Seed _ g).2 (TwoMode.alternate_rows Seed g)

theorem alternating_fold_iff_double {A B : Q} (g : A ⟶ B ⨿ A) :
    I (alternatingStep pe g) = coprod.desc (𝟙 A) (𝟙 A) ≫ I g ↔
      I (g ≫ coprod.desc coprod.inl g) = I g := by
  rw [← alternating_eq]
  exact TwoMode.alternate_uniform_iff Seed g

private theorem flipStep_iso (A : τ) {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    (modes pe A).hom ≫ flipStep pe A g =
      alternatingStep pe g ≫ coprod.map (𝟙 B) (modes pe A).hom := by
  rw [flipStep, Iso.hom_inv_id_assoc]

theorem flipStep_square (A : τ) {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    flipStep pe A g ≫ coprod.map (𝟙 B) (productFst Seed A Bit) = productFst Seed A Bit ≫ g := by
  apply (cancel_epi (modes pe A).hom).1
  rw [← Category.assoc (modes pe A).hom (flipStep pe A g), flipStep_iso pe,
    ← Category.assoc (modes pe A).hom (productFst Seed A Bit),
    Category.assoc (alternatingStep pe g), coprod.map_map, Category.id_comp, modes_fst]
  exact alternating_fold_square pe g

theorem flipStep_left (A : τ) {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    leftMode pe A ≫ flipStep pe A g = g ≫ coprod.map (𝟙 B) (rightMode pe A) := by
  rw [leftMode, Category.assoc, flipStep_iso pe, ← Category.assoc,
    alternatingStep, coprod.inl_desc, Category.assoc, coprod.map_map, Category.id_comp, rightMode]

theorem flipStep_right (A : τ) {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    rightMode pe A ≫ flipStep pe A g = g ≫ coprod.map (𝟙 B) (leftMode pe A) := by
  rw [rightMode, Category.assoc, flipStep_iso pe, ← Category.assoc,
    alternatingStep, coprod.inr_desc, Category.assoc, coprod.map_map, Category.id_comp, leftMode]

/-- Arbitrary alternating feedback reduces to the equality between one and two visible steps. -/
theorem flipStep_reset_iff (A : τ) {B : Q} (g : Obj A ⟶ B ⨿ Obj A) :
    I (flipStep pe A g) = I (flipStep pe A g ≫
      coprod.map (𝟙 B) (productFst Seed A Bit ≫ leftMode pe A)) ↔
      I (g ≫ coprod.desc coprod.inl g) = I g := by
  rw [iterate_reset_of_square Seed _ (leftMode pe A) (leftMode_fst pe A) _ g (flipStep_square pe A g),
    ← cancel_epi (modes pe A).hom, ← Category.assoc, modes_fst,
    ← uniformity_of_iso Seed (modes pe A) _ _ (flipStep_iso pe A g).symm]
  exact alternating_fold_iff_double pe g

theorem always_repeat_flip_reset (A : τ) (B : Q) :
    let g : Obj A ⟶ B ⨿ Obj A := coprod.inr
    let f := flipStep pe A g
    let p := productFst Seed A Bit
    HomProperty Seed p ∧
      (leftMode pe A ≫ f = rightMode pe A ≫ coprod.inr) ∧
      (rightMode pe A ≫ f = leftMode pe A ≫ coprod.inr) ∧
      f ≫ coprod.map (𝟙 B) p = p ≫ g ∧
      I f = I (f ≫ coprod.map (𝟙 B) (p ≫ leftMode pe A)) := by
  dsimp only
  refine ⟨fst_mem Seed A Bit, ?_, ?_, flipStep_square pe A _, ?_⟩
  · rw [flipStep_left, coprod.inr_map]
  · rw [flipStep_right, coprod.inr_map]
  · exact (flipStep_reset_iff pe A _).2 (by rw [coprod.inr_desc])


theorem iterate_double_of_no_repeat {A B : Q} (g : A ⟶ B ⨿ A) (k : A ⟶ B)
    (noRepeat : g ≫ coprod.desc coprod.inl g = k ≫ coprod.inl) :
    I (g ≫ coprod.desc coprod.inl g) = I g := by
  have unfoldTwice : (g ≫ coprod.desc coprod.inl g) ≫ coprod.desc (𝟙 B) (I g) = I g := by
    rw [Category.assoc, coprod.desc_comp, coprod.inl_desc,
      ← iterateChosen_fixpoint Seed g, ← iterateChosen_fixpoint Seed g]
  have g_eq : k = I g := by
    rw [noRepeat, Category.assoc, coprod.inl_desc, Category.comp_id] at unfoldTwice
    exact unfoldTwice
  rw [noRepeat, ← g_eq]
  conv_lhs => rw [iterateChosen_fixpoint Seed (k ≫ coprod.inl)]
  rw [Category.assoc, coprod.inl_desc, Category.comp_id]

theorem flipStep_reset_of_no_repeat (A : τ) {B : Q} (g : Obj A ⟶ B ⨿ Obj A) (k : Obj A ⟶ B)
    (noRepeat : g ≫ coprod.desc coprod.inl g = k ≫ coprod.inl) :
    I (flipStep pe A g) = I (flipStep pe A g ≫
      coprod.map (𝟙 B) (productFst Seed A Bit ≫ leftMode pe A)) :=
  (flipStep_reset_iff pe A g).2 (iterate_double_of_no_repeat pe g k noRepeat)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.HiddenBitFeedback
