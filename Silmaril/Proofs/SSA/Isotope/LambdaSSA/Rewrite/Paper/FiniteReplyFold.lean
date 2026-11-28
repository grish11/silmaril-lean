module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.HiddenBit.Unit.Thms

import Mathlib.Data.Fintype.Sum

/-! # Native discard replay for finite typed reply families -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FiniteReplyFold

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent (Route)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies
open Paper.WithCaseReturns.StructuralValues.HiddenBit (project_unit_row_comp_fold unit_fold_of_native_rows)

universe u v

variable {Φ : Type} [Profile Φ]

local notation "UT" => Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.FiniteReplies.UnitTy
local notation "U" => nativeUnit Φ
local notation "B" => nativeBit Φ
local notation "X" => unitObj Φ
local notation "S" => Seed Φ
local notation "F" => projection S
local notation "I" => iterateChosen S
local notation "reset" => Paper.TypeCategory.discardArrow (Φ := Φ) UT
local notation "drop" => Paper.TypeCategory.discardArrow (Φ := Φ) (coprod UT UT)

theorem code_finite (s : ReplyShape) : Finite s.Code := by
  induction s with
  | empty => exact inferInstanceAs (Finite Empty)
  | unit => exact inferInstanceAs (Finite Unit)
  | sum l r hl hr =>
      let _ : Finite l.Code := hl
      let _ : Finite r.Code := hr
      let _ : Fintype l.Code := Fintype.ofFinite _
      let _ : Fintype r.Code := Fintype.ofFinite _
      exact Finite.of_fintype (l.Code ⊕ r.Code)

set_option backward.isDefEq.respectTransparency false in
theorem dispatch_comp {Y Z : Native Φ} (s : ReplyShape)
    (k : s.Value → (U ⟶ Y)) (f : Y ⟶ Z) :
    dispatch s k ≫ f = dispatch s (fun x => k x ≫ f) := by
  induction s with
  | empty => exact Paper.TypeCategory.emptyIsInitial.hom_ext _ _
  | unit => rfl
  | sum l r hl hr =>
      simp only [dispatch, Category.assoc, coprod.desc_comp, hl, hr]

set_option backward.isDefEq.respectTransparency false in
private theorem render_comp {α : Type u} {Y Z : Native Φ} (r : Row Φ α)
    (leaf : α → (U ⟶ Y)) (f : Y ⟶ Z) :
    r.render leaf ≫ f = r.render (fun a => leaf a ≫ f) := by
  induction r with
  | leaf a => rfl
  | call p k ih =>
      rw [Row.render, Row.render, Category.assoc, dispatch_comp]
      simp only [ih]

private theorem render_map {α : Type u} {β : Type v} {Y : Native Φ} (r : Row Φ α)
    (leaf : β → (U ⟶ Y)) (f : α → β) :
    (r.map f).render leaf = r.render (fun a => leaf (f a)) := by
  induction r with
  | leaf a => rfl
  | call p k ih => simp only [Row.map, Row.render, ih]

set_option backward.isDefEq.respectTransparency false in
theorem native_erase (r : Row Φ Route) :
    r.render nativeRoute ≫ coprod.map (𝟙 U) drop = (r.map Route.recurrent).render nativeTarget := by
  have hl : (Paper.TypeCategory.sumCofan (Φ := Φ) UT UT).inl ≫ drop = reset := by
    rw [Paper.TypeCategory.sumCofan_inl]
    exact Paper.TypeCategory.discard_comp_branchValue (.inl (.var rfl))
  have hr : (Paper.TypeCategory.sumCofan (Φ := Φ) UT UT).inr ≫ drop = reset := by
    rw [Paper.TypeCategory.sumCofan_inr]
    exact Paper.TypeCategory.discard_comp_branchValue (.inr (.var rfl))
  rw [render_comp, render_map]
  congr 1
  funext a
  cases a
  · simp only [nativeRoute, nativeTarget, Route.recurrent, Category.assoc, coprod.inl_map, Category.id_comp]
  · rw [nativeRoute, Category.assoc, coprod.inr_map, ← Category.assoc, hl]
    rfl
  · rw [nativeRoute, Category.assoc, coprod.inr_map, ← Category.assoc, hr]
    rfl

private theorem include_unit {Γ : VCtx (Ty Atom)} {r s : Region Φ} {L : LCtx (Ty Atom)} :
    Paper.WithUnitEta.Step Γ r s L → S Γ r s L :=
  (Paper.WithPairReturns.StructuralValues.unitEta (Φ := Φ) false).out

private theorem project_erase (row : U ⟶ U ⨿ B) :
    projectRow row ≫ coprod.map (𝟙 X) fold =
      projectStep S (row ≫ coprod.map (𝟙 U) drop) :=
  project_unit_row_comp_fold S include_unit row

theorem erase_row (r : Row Φ Route) :
    projectRow (r.render nativeRoute) ≫ coprod.map (𝟙 X) fold = targetStep (r.map Route.recurrent) := by
  rw [project_erase, native_erase, targetStep]

open Semantics.Interaction.Typed
open Silmaril.Elgot.ITree
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Paper.Extension.Singleton.Generation (Coordinates)

attribute [local instance] typeModel categoricalInstructions

local notation "J" => typeJ (m := Tree Φ)
local notation "M" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)
local notation "K" => interpretation (Φ := Φ)

private noncomputable def eval {A D : Ty Atom}
    (f : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType D)
    (x : Ty.denote Atoms A) : Tree Φ (Ty.denote Atoms D) :=
  ((K).map ((F).map f)).of x

set_option backward.isDefEq.respectTransparency false in
private theorem eval_comp {A D E : Ty Atom}
    (f : Paper.TypeCategory.ofType (Φ := Φ) A ⟶ Paper.TypeCategory.ofType D)
    (g : Paper.TypeCategory.ofType (Φ := Φ) D ⟶ Paper.TypeCategory.ofType E)
    (x : Ty.denote Atoms A) :
    eval (f ≫ g) x = (eval f x >>= eval g) := by
  unfold eval
  rw [(F).map_comp, (K).map_comp, Kleisli.Type.comp_of_eq_kleisliRight]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem sum_comparison (A D : Ty Atom) :
    ((Coordinates.ofModel J M).sumIso A D).inv =
      (Kleisli.Type.coprodIsoSum (Tree Φ) ((J).obj ((M).obj A)) ((J).obj ((M).obj D))).hom := by
  let comparison := asIso (coprodComparison (J) ((M).obj A) ((M).obj D))
  let typeSum := Types.binaryCoproductIso ((M).obj A) ((M).obj D)
  have decode : ((M).coprodIso A D).inv = typeSum.hom := by
    change typeSum.hom ≫ 𝟙 _ = typeSum.hom
    rw [Category.comp_id]
  change comparison.hom ≫ (J).map ((M).coprodIso A D).inv = _
  rw [decode]
  apply coprod.hom_ext
  · simp only [comparison, asIso_hom, coprodComparison, coprod.inl_desc_assoc,
      Kleisli.Type.inl_coprodIsoSum_hom, ← Functor.map_comp, typeSum]
    rw [Types.binaryCoproductIso_inl_comp_hom]
    rfl
  · simp only [comparison, asIso_hom, coprodComparison, coprod.inr_desc_assoc,
      Kleisli.Type.inr_coprodIsoSum_hom, ← Functor.map_comp, typeSum]
    rw [Types.binaryCoproductIso_inr_comp_hom]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem eval_inl (A D : Ty Atom) (x : Ty.denote Atoms A) :
    eval (Paper.TypeCategory.sumCofan (Φ := Φ) A D).inl x =
      (pure (.inl x) : Tree Φ (Ty.denote Atoms (coprod A D))) := by
  let := regionTypingCoherent (raw (Φ := Φ)) compatible
  have h := (denoteFunctor_preserves (Φ := Φ) J M (fun _ _ => ⟨rfl, rfl⟩)
    (Paper.WithPairReturns.joined_seedDenotes (Φ := Φ) J M (fun _ _ => ⟨rfl, rfl⟩) false)).inl A D
  change 𝟙 _ ≫ (K).map ((F).map (Paper.TypeCategory.sumCofan (Φ := Φ) A D).inl) ≫ 𝟙 _ = _ at h
  rw [Category.comp_id, Category.id_comp, sum_comparison, Kleisli.Type.inl_coprodIsoSum_hom] at h
  exact congrArg (fun f => f.of x) h

set_option backward.isDefEq.respectTransparency false in
private theorem eval_inr (A D : Ty Atom) (x : Ty.denote Atoms D) :
    eval (Paper.TypeCategory.sumCofan (Φ := Φ) A D).inr x =
      (pure (.inr x) : Tree Φ (Ty.denote Atoms (coprod A D))) := by
  let := regionTypingCoherent (raw (Φ := Φ)) compatible
  have h := (denoteFunctor_preserves (Φ := Φ) J M (fun _ _ => ⟨rfl, rfl⟩)
    (Paper.WithPairReturns.joined_seedDenotes (Φ := Φ) J M (fun _ _ => ⟨rfl, rfl⟩) false)).inr A D
  change 𝟙 _ ≫ (K).map ((F).map (Paper.TypeCategory.sumCofan (Φ := Φ) A D).inr) ≫ 𝟙 _ = _ at h
  rw [Category.comp_id, Category.id_comp, sum_comparison, Kleisli.Type.inr_coprodIsoSum_hom] at h
  exact congrArg (fun f => f.of x) h

set_option backward.isDefEq.respectTransparency false in
private theorem eval_primitive (p : Φ) :
    eval (Paper.TypeCategory.primitiveReturn p) PUnit.unit =
      vis (Event.call p) (fun x => pure ((Profile.reply p).replyEquiv x)) := by
  let := regionTypingCoherent (raw (Φ := Φ)) compatible
  have h := denoteFunctor_map_primitive J M (fun _ _ => ⟨rfl, rfl⟩)
    (Paper.WithPairReturns.joined_seedDenotes (Φ := Φ) J M (fun _ _ => ⟨rfl, rfl⟩) false) p
  change 𝟙 _ ≫ (K).map ((F).map (Paper.TypeCategory.primitiveReturn p)) ≫ 𝟙 _ = _ at h
  rw [Category.comp_id, Category.id_comp] at h
  exact congrArg (fun f => f.of PUnit.unit) h

set_option backward.isDefEq.respectTransparency false in
private theorem eval_dispatch {D : Ty Atom} (s : ReplyShape)
    (k : s.Value → (U ⟶ Paper.TypeCategory.ofType D)) (x : s.Value) :
    eval (dispatch s k) x = eval (k x) PUnit.unit := by
  induction s with
  | empty => exact PEmpty.elim x
  | unit => cases x; rfl
  | sum l r hl hr =>
      cases x with
      | inl x =>
          have route : (Paper.TypeCategory.sumCofan l.ty r.ty).inl ≫ dispatch (.sum l r) k =
              dispatch l (fun y => k (.inl y)) := by
            rw [dispatch, ← Category.assoc, Paper.TypeCategory.sumCofan_inl_sumIso_hom, coprod.inl_desc]
          have h := congrArg (fun f => eval f x) route
          rw [eval_comp, eval_inl, pure_bind, hl] at h
          exact h
      | inr x =>
          have route : (Paper.TypeCategory.sumCofan l.ty r.ty).inr ≫ dispatch (.sum l r) k =
              dispatch r (fun y => k (.inr y)) := by
            rw [dispatch, ← Category.assoc, Paper.TypeCategory.sumCofan_inr_sumIso_hom, coprod.inr_desc]
          have h := congrArg (fun f => eval f x) route
          rw [eval_comp, eval_inr, pure_bind, hr] at h
          exact h

private abbrev Result := Ty.denote Atoms (coprod UT UT)

private def result : Bool → Result
  | false => .inl PUnit.unit
  | true => .inr PUnit.unit

private def observe : Row Φ Bool → Tree Φ Result
  | .leaf a => ret (result a)
  | .call p k => vis (Event.call p) (fun x => observe (k ((Profile.reply p).replyEquiv x)))

private def opcode {A : Type} : Event Φ A → Φ
  | .call p => p

private def head (v : Visible (Event Φ) Result (Tree Φ Result)) : Option Φ :=
  match v with
  | .ret _ => none
  | .vis e _ => some (opcode e)

private theorem observe_injective : Function.Injective (observe (Φ := Φ)) := by
  intro l
  induction l with
  | leaf a =>
      intro r eq
      cases r with
      | leaf b =>
          have h := ret_inj.mp eq
          cases a <;> cases b <;> simp_all [result]
      | call p k => exact (ret_ne_vis _ _ _ eq).elim
  | call p k ih =>
      intro r eq
      cases r with
      | leaf a => exact (ret_ne_vis _ _ _ eq.symm).elim
      | call q m =>
          have h := congrArg out eq
          simp only [observe, out_vis, Part.some_inj] at h
          have op : p = q := Option.some.inj (congrArg head h)
          subst q
          have step := (vis_inj (Event.call p) _ _).mp eq
          congr 1
          funext x
          obtain ⟨y, rfl⟩ := (Profile.reply p).replyEquiv.surjective x
          exact ih _ (congrFun step y)

set_option backward.isDefEq.respectTransparency false in
private theorem eval_reset : eval reset PUnit.unit = (pure PUnit.unit : Tree Φ PUnit.{2}) := by
  unfold eval
  rw [unit_eta_of_include S include_unit, (K).map_id]
  rfl

private theorem native_inl : (coprod.inl : U ⟶ U ⨿ U) ≫ (Paper.TypeCategory.sumIso UT UT).inv =
      (Paper.TypeCategory.sumCofan UT UT).inl := by
  apply (cancel_mono (Paper.TypeCategory.sumIso UT UT).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (Paper.TypeCategory.sumCofan_inl_sumIso_hom UT UT).symm

private theorem native_inr : (coprod.inr : U ⟶ U ⨿ U) ≫ (Paper.TypeCategory.sumIso UT UT).inv =
      (Paper.TypeCategory.sumCofan UT UT).inr := by
  apply (cancel_mono (Paper.TypeCategory.sumIso UT UT).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (Paper.TypeCategory.sumCofan_inr_sumIso_hom UT UT).symm

set_option backward.isDefEq.respectTransparency false in
private theorem target_tree (r : Row Φ Bool) :
    ((K).map (targetStep r ≫ (sumIso S UT UT).inv)).of PUnit.unit = observe r := by
  rw [targetStep, projectStep_comp_sumIso_inv]
  change eval (r.render nativeTarget ≫ (Paper.TypeCategory.sumIso UT UT).inv)
    PUnit.unit = observe r
  rw [render_comp]
  induction r with
  | leaf a =>
      cases a
      · rw [Row.render, nativeTarget, Category.assoc, native_inl, eval_comp, eval_reset, pure_bind, eval_inl]
        rfl
      · rw [Row.render, nativeTarget, Category.assoc, native_inr, eval_comp, eval_reset, pure_bind, eval_inr]
        rfl
  | call p k ih =>
      rw [Row.render, eval_comp, eval_primitive, vis_bind, observe]
      apply congrArg (vis (Event.call p))
      funext x
      rw [pure_bind, eval_dispatch, ih]

theorem target_injective : Function.Injective (targetStep (Φ := Φ)) := by
  intro l r eq
  apply observe_injective
  rw [← target_tree l, ← target_tree r, eq]

theorem square_iff (l r : Row Φ Route) (g : Row Φ Bool) :
    sourceStep l r ≫ coprod.map (𝟙 X) fold = fold ≫ targetStep g ↔
      l.map Route.recurrent = g ∧ r.map Route.recurrent = g := by
  constructor
  · intro eq
    constructor
    · apply target_injective
      rw [← erase_row]
      simpa only [sourceStep, coprod.inl_desc_assoc, Category.id_comp] using
        congrArg ((coprod.inl : X ⟶ X ⨿ X) ≫ ·) eq
    · apply target_injective
      rw [← erase_row]
      simpa only [sourceStep, coprod.inr_desc_assoc, Category.id_comp] using
        congrArg ((coprod.inr : X ⟶ X ⨿ X) ≫ ·) eq
  · rintro ⟨hl, hr⟩
    apply coprod.hom_ext
    · rw [sourceStep, coprod.inl_desc_assoc, erase_row, hl, coprod.inl_desc_assoc, Category.id_comp]
    · rw [sourceStep, coprod.inr_desc_assoc, erase_row, hr, coprod.inr_desc_assoc, Category.id_comp]

theorem square_iff_native (l r : Row Φ Route) (g : Row Φ Bool) :
    sourceStep l r ≫ coprod.map (𝟙 X) fold = fold ≫ targetStep g ↔
      l.render nativeRoute ≫ coprod.map (𝟙 U) drop = g.render nativeTarget ∧
      r.render nativeRoute ≫ coprod.map (𝟙 U) drop = g.render nativeTarget := by
  constructor
  · intro sq
    obtain ⟨hl, hr⟩ := (square_iff l r g).1 sq
    exact ⟨(native_erase l).trans (congrArg (Row.render nativeTarget) hl),
      (native_erase r).trans (congrArg (Row.render nativeTarget) hr)⟩
  · rintro ⟨hl, hr⟩
    apply coprod.hom_ext
    · rw [sourceStep, coprod.inl_desc_assoc, project_erase, hl,
        coprod.inl_desc_assoc, Category.id_comp, targetStep]
    · rw [sourceStep, coprod.inr_desc_assoc, project_erase, hr,
        coprod.inr_desc_assoc, Category.id_comp, targetStep]

theorem uniformity (l r : Row Φ Route) (g : Row Φ Bool)
    (square : sourceStep l r ≫ coprod.map (𝟙 X) fold = fold ≫ targetStep g) :
    I (sourceStep l r) = fold ≫ I (targetStep g) := by
  obtain ⟨hl, hr⟩ := (square_iff_native l r g).1 square
  exact unit_fold_of_native_rows S include_unit (l.render nativeRoute) (r.render nativeRoute)
    (g.render nativeTarget) hl hr

theorem example_codes : Example.right.map Route.recurrent = Example.target := by
  simp only [Example.right, Example.target, Example.left, Example.row, Row.map]
  congr 1
  funext x
  rcases x with x | x | x
  · rfl
  · rfl
  · simp only [Row.map]
    congr 1
    funext y
    rcases y with y | y | y <;> rfl

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.FiniteReplyFold
