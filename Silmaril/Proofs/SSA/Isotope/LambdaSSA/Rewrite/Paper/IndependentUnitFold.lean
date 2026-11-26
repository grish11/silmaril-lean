module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent.Defs
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.StructuralValues.Freyd.Iteration.Elgot.Projection.HiddenBit.Unit.Thms

/-! # Replay of independent finite visible rows in standard Paper -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IndependentUnitFold

open Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits Silmaril.Elgot.ITree
open Paper.Extension.Singleton
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Independent
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible
  (Atom Atoms Op Event Seed Two Tree choose replyIso replyValue interpretation reply_tags_tree choose_copair_tree)

local notation "Uty" => Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible.UnitTy
local notation "Uq" => Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible.One
local notation "Q" => TypeCategory Seed
local notation "I" => iterateChosen Seed
local notation "F" => projection Seed

private theorem render_comp {C : Type*} [Category C] [HasBinaryCoproducts C] {U Y Z : C}
    {α : Type} (r : ReplyTree α) (request : U ⟶ U ⨿ U) (leaf : α → (U ⟶ Y)) (f : Y ⟶ Z) :
    r.render request leaf ≫ f = r.render request (fun a => leaf a ≫ f) := by
  induction r with
  | leaf a => rfl
  | poll l r hl hr => simp only [ReplyTree.render, Category.assoc, coprod.desc_comp, hl, hr]

private theorem render_map {C : Type*} [Category C] [HasBinaryCoproducts C] {U Y : C}
    {α β : Type} (r : ReplyTree α) (request : U ⟶ U ⨿ U) (leaf : β → (U ⟶ Y)) (f : α → β) :
    (r.map f).render request leaf = r.render request (fun a => leaf (f a)) := by
  induction r with
  | leaf a => rfl
  | poll l r hl hr => simp only [ReplyTree.map, ReplyTree.render, hl, hr]

theorem erase_row (r : ReplyTree Route) :
    r.render request route ≫ coprod.map (𝟙 Uq) fold = targetStep (r.map Route.recurrent) := by
  rw [render_comp, targetStep, render_map]
  congr 1
  funext a
  cases a <;> simp [route, foldedRoute, Route.recurrent, fold, Category.assoc]

private def observe : ReplyTree Bool → Tree (Ty.denote Atoms (Silmaril.coprod Uty Uty))
  | .leaf b => ret (replyValue b)
  | .poll l r => vis .poll (fun b => if b then observe r else observe l)

private theorem reply_inl : coprod.inl ≫ replyIso.inv = (sumCofan Seed Uty Uty).inl := by
  apply (cancel_mono replyIso.hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (sumCofan_inl_sumIso_hom Seed Uty Uty).symm

private theorem reply_inr : coprod.inr ≫ replyIso.inv = (sumCofan Seed Uty Uty).inr := by
  apply (cancel_mono replyIso.hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (sumCofan_inr_sumIso_hom Seed Uty Uty).symm

set_option backward.isDefEq.respectTransparency false in
private theorem target_tree (r : ReplyTree Bool) :
    (interpretation.map (targetStep r ≫ replyIso.inv)).of PUnit.unit = observe r := by
  rw [targetStep, render_comp]
  induction r with
  | leaf a =>
      cases a
      · change (interpretation.map (coprod.inl ≫ replyIso.inv)).of PUnit.unit = _
        rw [reply_inl]
        exact reply_tags_tree.1
      · change (interpretation.map (coprod.inr ≫ replyIso.inv)).of PUnit.unit = _
        rw [reply_inr]
        exact reply_tags_tree.2
  | poll l r hl hr =>
      rw [ReplyTree.render, Category.assoc, choose_copair_tree, observe]
      apply congrArg (vis Event.poll)
      funext b
      cases b
      · exact hl
      · exact hr

private theorem observe_injective : Function.Injective observe := by
  intro l
  induction l with
  | leaf a =>
      intro r h
      cases r with
      | leaf b =>
          have eq := ret_inj.mp h
          cases a <;> cases b <;> simp_all [replyValue]
      | poll l r =>
          exact (ret_ne_vis _ _ _ h).elim
  | poll l r hl hr =>
      intro s h
      cases s with
      | leaf b =>
          exact (ret_ne_vis _ _ _ h.symm).elim
      | poll l' r' =>
          have eq := (vis_inj Event.poll _ _).mp h
          have el : observe l = observe l' := congrFun eq false
          have er : observe r = observe r' := congrFun eq true
          rw [hl el, hr er]

set_option backward.isDefEq.respectTransparency false in
theorem target_injective : Function.Injective targetStep := by
  intro l r eq
  apply observe_injective
  rw [← target_tree l, ← target_tree r, eq]

theorem square_iff (l r : ReplyTree Route) (g : ReplyTree Bool) :
    sourceStep l r ≫ coprod.map (𝟙 Uq) fold = fold ≫ targetStep g ↔
      l.map Route.recurrent = g ∧ r.map Route.recurrent = g := by
  constructor
  · intro h
    constructor
    · apply target_injective
      rw [← erase_row]
      simpa only [sourceStep, coprod.inl_desc_assoc, Category.id_comp] using
        congrArg ((coprod.inl : Uq ⟶ Uq ⨿ Uq) ≫ ·) h
    · apply target_injective
      rw [← erase_row]
      simpa only [sourceStep, coprod.inr_desc_assoc, Category.id_comp] using
        congrArg ((coprod.inr : Uq ⟶ Uq ⨿ Uq) ≫ ·) h
  · rintro ⟨hl, hr⟩
    apply coprod.hom_ext
    · rw [sourceStep, coprod.inl_desc_assoc, erase_row, hl, coprod.inl_desc_assoc, Category.id_comp]
    · rw [sourceStep, coprod.inr_desc_assoc, erase_row, hr, coprod.inr_desc_assoc, Category.id_comp]

local notation "P" => Paper.TypeCategory (τ := Ty Atom) Op
local notation "U" => Paper.TypeCategory.ofType (Φ := Op) Uty
local notation "T" => Paper.TypeCategory.ofType (Φ := Op) (Silmaril.coprod Uty Uty)
local notation "c" => PreservesColimitPair.iso F
local notation "reset" => Paper.TypeCategory.discardArrow (Φ := Op) Uty
local notation "drop" => Paper.TypeCategory.discardArrow (Φ := Op) (Silmaril.coprod Uty Uty)

private abbrev tagL : U ⟶ T := (Paper.TypeCategory.sumCofan Uty Uty).inl
private abbrev tagR : U ⟶ T := (Paper.TypeCategory.sumCofan Uty Uty).inr

private noncomputable abbrev nativeRequest : U ⟶ U ⨿ U :=
  Paper.TypeCategory.primitiveReturn Op.choose ≫ (Paper.TypeCategory.sumIso Uty Uty).hom

private noncomputable def nativeRoute : Route → (U ⟶ U ⨿ T)
  | .exit => reset ≫ coprod.inl
  | .first => tagL ≫ coprod.inr
  | .second => tagR ≫ coprod.inr

private noncomputable def nativeFolded : Bool → (U ⟶ U ⨿ U)
  | false => reset ≫ coprod.inl
  | true => reset ≫ coprod.inr

private theorem native_erase (row : ReplyTree Route) :
    row.render nativeRequest nativeRoute ≫ coprod.map (𝟙 U) drop =
      (row.map Route.recurrent).render nativeRequest nativeFolded := by
  have hl : tagL ≫ drop = reset := by
    unfold tagL
    rw [Paper.TypeCategory.sumCofan_inl]
    exact Paper.TypeCategory.discard_comp_branchValue (.inl (.var rfl))
  have hr : tagR ≫ drop = reset := by
    unfold tagR
    rw [Paper.TypeCategory.sumCofan_inr]
    exact Paper.TypeCategory.discard_comp_branchValue (.inr (.var rfl))
  rw [render_comp, render_map]
  congr 1
  funext a
  cases a
  · simp only [nativeRoute, nativeFolded, Route.recurrent, Category.assoc, coprod.inl_map, Category.id_comp]
  · rw [nativeRoute, Category.assoc, coprod.inr_map, ← Category.assoc, hl]
    rfl
  · rw [nativeRoute, Category.assoc, coprod.inr_map, ← Category.assoc, hr]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem project_request : (F).map nativeRequest = request ≫ (c U U).hom := by
  have eq := congrArg Iso.hom (projection_mapIso_sumIso Seed Uty Uty)
  change (F).map (Paper.TypeCategory.sumIso Uty Uty).hom = replyIso.hom ≫ (c U U).hom at eq
  rw [nativeRequest, (F).map_comp, eq, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
private theorem compare_desc {Y : P} (l r : U ⟶ Y) :
    (c U U).hom ≫ (F).map (coprod.desc l r) = coprod.desc ((F).map l) ((F).map r) := by
  rw [PreservesColimitPair.iso_hom]
  apply coprod.hom_ext
  · rw [inl_coprodComparison_assoc, ← (F).map_comp, coprod.inl_desc, coprod.inl_desc]
  · rw [inr_coprodComparison_assoc, ← (F).map_comp, coprod.inr_desc, coprod.inr_desc]

set_option backward.isDefEq.respectTransparency false in
private theorem project_render {α : Type} {Y : P} (leaf : α → (U ⟶ Y)) (r : ReplyTree α) :
    (F).map (r.render nativeRequest leaf) = r.render request (fun a => (F).map (leaf a)) := by
  induction r with
  | leaf a => rfl
  | poll l r hl hr =>
      rw [ReplyTree.render, ReplyTree.render, (F).map_comp, project_request, Category.assoc,
        compare_desc, hl, hr]

set_option backward.isDefEq.respectTransparency false in
private theorem project_inl (A B : P) :
    (F).map (coprod.inl : A ⟶ A ⨿ B) ≫ (c A B).inv = coprod.inl := by
  apply (cancel_mono (c A B).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, PreservesColimitPair.iso_hom, inl_coprodComparison]

set_option backward.isDefEq.respectTransparency false in
private theorem project_inr (A B : P) :
    (F).map (coprod.inr : B ⟶ A ⨿ B) ≫ (c A B).inv = coprod.inr := by
  apply (cancel_mono (c A B).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, PreservesColimitPair.iso_hom, inr_coprodComparison]

private theorem eta : (F).map reset = 𝟙 Uq :=
  unit_eta_of_include Seed (Paper.WithPairReturns.StructuralValues.unitEta false).out

set_option backward.isDefEq.respectTransparency false in
private theorem project_native_row (row : ReplyTree Route) :
    (F).map (row.render nativeRequest nativeRoute) ≫ (c U T).inv ≫ coprod.map (𝟙 Uq) replyIso.hom =
      row.render request route := by
  rw [project_render, render_comp]
  congr 1
  funext a
  cases a
  · rw [nativeRoute, (F).map_comp, eta, Category.id_comp, ← Category.assoc, project_inl]
    simp only [route, coprod.inl_map, Category.id_comp]
  · rw [nativeRoute, (F).map_comp, Category.assoc, ← Category.assoc ((F).map coprod.inr),
      project_inr, coprod.inr_map, ← Category.assoc]
    rw [show (F).map tagL ≫ replyIso.hom = coprod.inl from sumCofan_inl_sumIso_hom Seed Uty Uty]
    rfl
  · rw [nativeRoute, (F).map_comp, Category.assoc, ← Category.assoc ((F).map coprod.inr),
      project_inr, coprod.inr_map, ← Category.assoc]
    rw [show (F).map tagR ≫ replyIso.hom = coprod.inr from sumCofan_inr_sumIso_hom Seed Uty Uty]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem project_native_target (g : ReplyTree Bool) :
    projectStep Seed (g.render nativeRequest nativeFolded) = targetStep g := by
  change (F).map (g.render nativeRequest nativeFolded) ≫ (c U U).inv = _
  rw [project_render, render_comp, targetStep]
  congr 1
  funext a
  cases a
  · rw [nativeFolded, (F).map_comp, eta, Category.id_comp, project_inl, foldedRoute]
  · rw [nativeFolded, (F).map_comp, eta, Category.id_comp, project_inr, foldedRoute]

set_option backward.isDefEq.respectTransparency false in
theorem uniformity (l r : ReplyTree Route) (g : ReplyTree Bool)
    (square : sourceStep l r ≫ coprod.map (𝟙 Uq) fold = fold ≫ targetStep g) :
    I (sourceStep l r) = fold ≫ I (targetStep g) := by
  obtain ⟨hl, hr⟩ := (square_iff l r g).1 square
  have eq := Paper.WithCaseReturns.StructuralValues.HiddenBit.unit_fold_of_native_rows Seed
    (Paper.WithPairReturns.StructuralValues.unitEta false).out
    (l.render nativeRequest nativeRoute) (r.render nativeRequest nativeRoute)
    (g.render nativeRequest nativeFolded)
    ((native_erase l).trans (congrArg (fun t => t.render nativeRequest nativeFolded) hl))
    ((native_erase r).trans (congrArg (fun t => t.render nativeRequest nativeFolded) hr))
  simpa only [sourceStep, project_native_row, project_native_target] using eq

theorem mixed_identity (l r : ReplyTree Route) (g : ReplyTree Bool)
    (square : sourceStep l r ≫ coprod.map (𝟙 Uq) fold = fold ≫ targetStep g) :
    let a := sourceStep l r ≫ (coprod.associator Uq Uq Uq).inv
    I ((coprod.inl ≫ a) ≫ coprod.desc (𝟙 (Uq ⨿ Uq)) (I (coprod.inr ≫ a))) = I (targetStep g) := by
  let i := coprod.associator Uq Uq Uq
  let a := sourceStep l r ≫ i.inv
  have cmp : i.inv ≫ coprod.desc (𝟙 (Uq ⨿ Uq)) coprod.inr = coprod.map (𝟙 Uq) fold := by
    apply (cancel_epi i.hom).1
    rw [Iso.hom_inv_id_assoc]
    apply coprod.hom_ext
    · apply coprod.hom_ext <;> simp [i, coprod.associator, fold]
    · simp [i, coprod.associator, fold]
  have row : (coprod.inr ≫ a) ≫ coprod.desc (𝟙 (Uq ⨿ Uq)) coprod.inr = targetStep g := by
    simp only [a, Category.assoc, cmp, square, fold, coprod.inr_desc_assoc, Category.id_comp]
  apply (Paper.WithCaseReturns.StructuralValues.HiddenBit.binary_fold_iff_mixed_of_seed Seed a
    (targetStep g) row).1
  change I ((sourceStep l r ≫ i.inv) ≫ i.hom) = fold ≫ I (targetStep g)
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact uniformity l r g square

private noncomputable def testRoute (p : Route → Bool) : Uq ⨿ (Uq ⨿ Uq) ⟶ Uq ⨿ Uq :=
  coprod.desc (foldedRoute (p .exit)) (coprod.desc (foldedRoute (p .first)) (foldedRoute (p .second)))

private theorem test_row (r : ReplyTree Route) (p : Route → Bool) :
    r.render request route ≫ testRoute p = targetStep (r.map p) := by
  rw [render_comp, targetStep, render_map]
  congr 1
  funext a
  cases a <;> simp only [route, testRoute, Category.assoc, coprod.inl_desc, coprod.inr_desc]

local notation "swapCopies" => coprod.map (𝟙 Uq) (coprod.desc
  (coprod.inr : Uq ⟶ Uq ⨿ Uq) coprod.inl)

private theorem swap_row (r : ReplyTree Route) :
    r.render request route ≫ swapCopies = (r.map Route.swap).render request route := by
  rw [render_comp, render_map]
  congr 1
  funext a
  cases a <;> simp [route, Route.swap, Category.assoc]

theorem fixture_no_swap :
    ¬ ∃ decision : Uq ⟶ Uq ⨿ (Uq ⨿ Uq),
      sourceStep fixtureLeft fixtureRight = coprod.desc decision (decision ≫ swapCopies) := by
  rintro ⟨decision, eq⟩
  have left : fixtureLeft.render request route = decision := by
    simpa only [sourceStep, coprod.inl_desc] using congrArg ((coprod.inl : Uq ⟶ Uq ⨿ Uq) ≫ ·) eq
  have right : fixtureRight.render request route = decision ≫ swapCopies := by
    simpa only [sourceStep, coprod.inr_desc] using congrArg ((coprod.inr : Uq ⟶ Uq ⨿ Uq) ≫ ·) eq
  rw [← left, swap_row] at right
  let isFirst : Route → Bool := fun a => decide (a = .first)
  have obs := congrArg (· ≫ testRoute isFirst) right
  rw [test_row, test_row] at obs
  have distinct : fixtureRight.map isFirst ≠ (fixtureLeft.map Route.swap).map isFirst := by decide
  exact distinct (target_injective obs)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.IndependentUnitFold
