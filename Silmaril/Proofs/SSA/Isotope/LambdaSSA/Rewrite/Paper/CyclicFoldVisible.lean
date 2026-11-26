module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible.Defs

/-! # The guarded two-cycle and its visible back edges -/

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CyclicFoldVisible

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA Silmaril.Isotope.LambdaSSA.Region
open CategoryTheory CategoryTheory.Limits
open Paper.Extension.Singleton (iterateChosen iterateChosen_fixpoint denoteFunctor_map_primitive)
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic
open Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible

local notation "Uty" => Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible.UnitTy
local notation "Uobj" => Visible.One
local notation "fold" => foldState Seed Uty

theorem square : sourceStep ≫ coprod.map (𝟙 Uobj) fold = fold ≫ targetStep := by
  apply (fold_square_iff Seed Uty sourceRows targetRows).2
  let k : Uobj ⨿ Uobj ⟶ Uobj := coprod.desc (𝟙 Uobj) (𝟙 Uobj)
  change sourceRows ≫ coprod.map (𝟙 (Uobj ⨿ Uobj)) k = coprod.map (𝟙 Uobj) k ≫ targetRows
  simp only [sourceRows, targetRows, coprod.desc_comp, coprod.map_desc, Category.assoc,
    coprod.inl_map, coprod.inr_map, k, coprod.inl_desc, coprod.inr_desc, Category.id_comp]

theorem iteration :
    iterateChosen Seed sourceStep = fold ≫ iterateChosen Seed targetStep := by
  apply uniformity_of_right_switch Seed Uty (Paper.WithPairReturns.StructuralValues.unitEta false).out
      sourceRows targetRows square
  simp only [sourceRows, targetRows, coprod.inr_desc, coprod.inr_map, Category.assoc]

private theorem source_edge {input output : Uobj ⟶ Uobj ⨿ Uobj}
    (edge : input ≫ coprod.inr ≫ sourceRows =
      poll ≫ output ≫ (coprod.inr : Uobj ⨿ Uobj ⟶ (Uobj ⨿ Uobj) ⨿ (Uobj ⨿ Uobj))) :
    (input ≫ coprod.inr ≫ (sourceIso Seed Uty).inv) ≫ sourceStep =
      poll ≫ (output ≫ coprod.inr ≫ (sourceIso Seed Uty).inv) ≫ (coprod.inr : Three ⟶ Uobj ⨿ Three) := by
  let iso : Three ≅ Uobj ⨿ (Uobj ⨿ Uobj) := sourceIso Seed Uty
  let assoc := coprod.associator Uobj Uobj (Uobj ⨿ Uobj)
  change (input ≫ coprod.inr ≫ iso.inv) ≫
      (iso.hom ≫ sourceRows ≫ assoc.hom ≫ coprod.map (𝟙 Uobj) iso.inv) =
      poll ≫ (output ≫ coprod.inr ≫ iso.inv) ≫ coprod.inr
  simp only [Category.assoc, Iso.inv_hom_id_assoc, reassoc_of% edge]
  simp [assoc, coprod.associator, Category.assoc]

theorem first_edge :
    firstMode ≫ sourceStep = poll ≫ secondMode ≫ (coprod.inr : Three ⟶ Uobj ⨿ Three) := by
  apply source_edge
  rw [sourceRows, coprod.inr_desc, coprod.inl_desc]

theorem second_edge :
    secondMode ≫ sourceStep = poll ≫ firstMode ≫ (coprod.inr : Three ⟶ Uobj ⨿ Three) := by
  apply source_edge
  simp only [sourceRows, coprod.inr_desc]

theorem target_edge :
    foldedMode ≫ targetStep = poll ≫ foldedMode ≫ (coprod.inr : Two ⟶ Uobj ⨿ Two) := by
  let iso : Two ≅ Uobj ⨿ Uobj := targetIso Seed Uty
  change (coprod.inr ≫ iso.inv) ≫
      (iso.hom ≫ targetRows ≫ (coprod.associator Uobj Uobj Uobj).hom ≫ coprod.map (𝟙 Uobj) iso.inv) =
      poll ≫ (coprod.inr ≫ iso.inv) ≫ coprod.inr
  simp only [Category.assoc, Iso.inv_hom_id_assoc, targetRows, coprod.inr_desc_assoc]
  simp [coprod.associator, Category.assoc]

theorem fold_modes : firstMode ≫ fold = foldedMode ∧ secondMode ≫ fold = foldedMode := by
  let iso : Three ≅ Uobj ⨿ (Uobj ⨿ Uobj) := sourceIso Seed Uty
  let tgt : Two ≅ Uobj ⨿ Uobj := targetIso Seed Uty
  have eq := congrArg (fun f => iso.inv ≫ f)
    (fold_coordinates Seed Uty)
  have route :
      iso.inv ≫ fold ≫ tgt.hom =
        coprod.map (𝟙 Uobj) (coprod.desc (𝟙 Uobj) (𝟙 Uobj)) := by
    change iso.inv ≫ iso.hom ≫ _ = iso.inv ≫ fold ≫ tgt.hom at eq
    rw [Iso.inv_hom_id_assoc] at eq
    exact eq.symm
  constructor
  · apply (cancel_mono tgt.hom).mp
    change ((coprod.inl ≫ coprod.inr ≫ iso.inv) ≫ fold) ≫ tgt.hom = (coprod.inr ≫ tgt.inv) ≫ tgt.hom
    simp only [Category.assoc, route, coprod.inr_map, coprod.inl_desc_assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  · apply (cancel_mono tgt.hom).mp
    change ((coprod.inr ≫ coprod.inr ≫ iso.inv) ≫ fold) ≫ tgt.hom = (coprod.inr ≫ tgt.inv) ≫ tgt.hom
    simp only [Category.assoc, route, coprod.inr_map, coprod.inr_desc_assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]

open Semantics.Interaction.Typed
open Silmaril.Elgot.ITree
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)

attribute [local instance] typeModel categoricalInstructions

local notation "J" => typeJ (m := Tree)
local notation "M" => Semantics.Categorical.ofMonadicTypeModel (τ := Ty Atom)
local notation "F" => interpretation

set_option backward.isDefEq.respectTransparency false in
theorem poll_image (x : PUnit.{2}) :
    ((F).map poll).of x = vis .poll (fun _ => pure PUnit.unit) := by
  let := regionTypingCoherent raw compatible
  have p := denoteFunctor_map_primitive J M (fun _ _ => ⟨rfl, rfl⟩)
    (Paper.WithPairReturns.joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false) Op.poll
  change 𝟙 _ ≫ (F).map poll ≫ 𝟙 _ = _ at p
  rw [Category.comp_id, Category.id_comp] at p
  exact congrArg (fun f => f.of x) p

private theorem poll_ne_id : poll ≠ 𝟙 Uobj := by
  intro eq
  have h : ((F).map poll).of PUnit.unit = (pure PUnit.unit : Tree PUnit.{2}) := by
    rw [eq, (F).map_id]
    rfl
  rw [poll_image] at h
  have outEq := congrArg out h
  change _ = out (ret (E := Event) PUnit.unit) at outEq
  rw [out_vis, out_ret] at outEq
  have h' := Part.some_inj.mp outEq
  cases h'

theorem modes_ne : firstMode ≠ secondMode := by
  intro eq
  let distinguish : Three ⟶ Uobj :=
    (sourceIso Seed Uty).hom ≫ coprod.desc (𝟙 Uobj) (coprod.desc (𝟙 Uobj) poll)
  have h := congrArg (· ≫ distinguish) eq
  let iso : Three ≅ Uobj ⨿ (Uobj ⨿ Uobj) := sourceIso Seed Uty
  have hl : firstMode ≫ distinguish = 𝟙 Uobj := by
    change (coprod.inl ≫ coprod.inr ≫ iso.inv) ≫
      (iso.hom ≫ coprod.desc (𝟙 Uobj) (coprod.desc (𝟙 Uobj) poll)) = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, coprod.inr_desc, coprod.inl_desc]
  have hr : secondMode ≫ distinguish = poll := by
    change (coprod.inr ≫ coprod.inr ≫ iso.inv) ≫
      (iso.hom ≫ coprod.desc (𝟙 Uobj) (coprod.desc (𝟙 Uobj) poll)) = _
    simp only [Category.assoc, Iso.inv_hom_id_assoc, coprod.inr_desc]
  rw [hl, hr] at h
  exact poll_ne_id h.symm

theorem fold_not_mono : ¬ Mono fold := fun _ =>
  modes_ne ((cancel_mono fold).mp (fold_modes.1.trans fold_modes.2.symm))

set_option backward.isDefEq.respectTransparency false in
private theorem feedback_poll {enter next : Uobj ⟶ Three}
    (edge : enter ≫ sourceStep = poll ≫ next ≫ (coprod.inr : Three ⟶ Uobj ⨿ Three)) :
    out (runFrom enter) = Part.some (.vis Event.poll (fun _ => runFrom next)) := by
  let result := iterateChosen Seed sourceStep
  have step : enter ≫ result = poll ≫ (next ≫ result) := calc
    enter ≫ result = enter ≫ sourceStep ≫ coprod.desc (𝟙 Uobj) result :=
      congrArg (enter ≫ ·) (iterateChosen_fixpoint Seed sourceStep)
    _ = _ := by rw [← Category.assoc enter, edge]; simp only [Category.assoc, coprod.inr_desc]
  change out (((F).map (enter ≫ result)).of PUnit.unit : Tree PUnit.{2}) = _
  rw [step, (F).map_comp, Kleisli.Type.comp_of_eq_kleisliRight]
  change out ((((F).map poll).of PUnit.unit >>= fun x => ((F).map (next ≫ result)).of x) : Tree PUnit.{2}) = _
  rw [poll_image, vis_bind, out_vis]
  refine congrArg Part.some (congrArg (Silmaril.Elgot.ITree.Visible.vis Event.poll) (funext fun _ => ?_))
  exact pure_bind (m := Tree) _ _

theorem first_visible :
    out (runFrom firstMode) = Part.some (.vis Event.poll (fun _ => runFrom secondMode)) :=
  feedback_poll first_edge

theorem second_visible :
    out (runFrom secondMode) = Part.some (.vis Event.poll (fun _ => runFrom firstMode)) :=
  feedback_poll second_edge

theorem mixed_square : mixedSourceStep ≫ coprod.map (𝟙 Uobj) fold = fold ≫ mixedTargetStep := by
  apply (fold_square_iff Seed Uty mixedSourceRows mixedTargetRows).2
  let k : Uobj ⨿ Uobj ⟶ Uobj := coprod.desc (𝟙 Uobj) (𝟙 Uobj)
  have swapFold : coprod.desc coprod.inr coprod.inl ≫ k = k :=
    coprod.hom_ext (by simp [k]) (by simp [k])
  change mixedSourceRows ≫ coprod.map (𝟙 (Uobj ⨿ Uobj)) k =
    coprod.map (𝟙 Uobj) k ≫ mixedTargetRows
  apply coprod.hom_ext
  · rw [mixedSourceRows, mixedTargetRows, coprod.inl_desc_assoc,
      coprod.inl_map_assoc, Category.id_comp, coprod.inl_desc]
    simp only [Category.assoc, coprod.inl_map, Category.id_comp]
  · rw [mixedSourceRows, mixedTargetRows, coprod.inr_desc_assoc, coprod.inr_map_assoc,
      coprod.inr_desc]
    apply coprod.hom_ext
    · rw [coprod.inl_desc_assoc, coprod.inl_desc_assoc, Category.id_comp]
    · rw [coprod.inr_desc_assoc, coprod.inr_desc_assoc, Category.id_comp, Category.assoc,
        coprod.map_map, Category.id_comp, swapFold]

theorem mixed_iteration :
    iterateChosen Seed mixedSourceStep = fold ≫ iterateChosen Seed mixedTargetStep := by
  apply uniformity_of_shared_choice Seed Uty (Paper.WithPairReturns.StructuralValues.unitEta false).out
    mixedSourceRows mixedTargetRows mixed_square decision
  exact coprod.inr_desc _ _

set_option backward.isDefEq.respectTransparency false in
private theorem mixed_source_route :
    (coprod.inr : Uobj ⨿ Uobj ⟶ (Uobj ⨿ Uobj) ⨿ (Uobj ⨿ Uobj)) ≫
        (coprod.associator Uobj Uobj (Uobj ⨿ Uobj)).hom ≫
        coprod.map (𝟙 Uobj) (sourceIso Seed Uty).inv =
      coprod.desc (firstMode ≫ (coprod.inr : Three ⟶ Uobj ⨿ Three)) (secondMode ≫ coprod.inr) := by
  let iso : Three ≅ Uobj ⨿ (Uobj ⨿ Uobj) := sourceIso Seed Uty
  let assoc := coprod.associator Uobj Uobj (Uobj ⨿ Uobj)
  have route : coprod.inr ≫ assoc.hom ≫ coprod.map (𝟙 Uobj) iso.inv =
      coprod.inr ≫ iso.inv ≫ coprod.inr := by
    simp only [assoc, coprod.associator, Category.assoc, coprod.inr_desc_assoc, coprod.inr_map]
  rw [route]
  apply coprod.hom_ext
  · simp only [coprod.inl_desc, firstMode, Category.assoc, iso]
  · simp only [coprod.inr_desc, secondMode, Category.assoc, iso]

theorem mixed_first_edge :
    firstMode ≫ mixedSourceStep = choose ≫ replyIso.hom ≫
      coprod.desc (firstMode ≫ (coprod.inr : Three ⟶ Uobj ⨿ Three)) (secondMode ≫ coprod.inr) := by
  simp only [firstMode, mixedSourceStep, realize, Category.assoc, Iso.inv_hom_id_assoc,
    mixedSourceRows, coprod.inr_desc_assoc, coprod.inl_desc_assoc, decision]
  simpa only [firstMode, secondMode, Category.assoc] using
    congrArg (fun f => choose ≫ replyIso.hom ≫ f) mixed_source_route

theorem mixed_second_edge :
    secondMode ≫ mixedSourceStep = choose ≫ replyIso.hom ≫
      coprod.desc (secondMode ≫ (coprod.inr : Three ⟶ Uobj ⨿ Three)) (firstMode ≫ coprod.inr) := by
  have swapRoute :
      coprod.desc (coprod.inr : Uobj ⟶ Uobj ⨿ Uobj) coprod.inl ≫
        coprod.desc (firstMode ≫ (coprod.inr : Three ⟶ Uobj ⨿ Three)) (secondMode ≫ coprod.inr) =
      coprod.desc (secondMode ≫ coprod.inr) (firstMode ≫ coprod.inr) := by
    rw [coprod.desc_comp, coprod.inr_desc, coprod.inl_desc]
  simp only [secondMode, mixedSourceStep, realize, Category.assoc, Iso.inv_hom_id_assoc,
    mixedSourceRows, coprod.inr_desc_assoc, decision, coprod.inr_map_assoc]
  simpa only [firstMode, secondMode, Category.assoc] using
    congrArg (fun f => choose ≫ replyIso.hom ≫ f)
      ((congrArg (coprod.desc (coprod.inr : Uobj ⟶ Uobj ⨿ Uobj) coprod.inl ≫ ·)
        mixed_source_route).trans swapRoute)

set_option backward.isDefEq.respectTransparency false in
theorem choose_image (x : PUnit.{2}) :
    ((F).map choose).of x = vis .poll (fun b => pure (replyValue b)) := by
  let := regionTypingCoherent raw compatible
  have p := denoteFunctor_map_primitive J M (fun _ _ => ⟨rfl, rfl⟩)
    (Paper.WithPairReturns.joined_seedDenotes J M (fun _ _ => ⟨rfl, rfl⟩) false) Op.choose
  change 𝟙 _ ≫ (F).map choose ≫ 𝟙 _ = _ at p
  rw [Category.comp_id, Category.id_comp] at p
  exact congrArg (fun f => f.of x) p

open Paper.Extension.Singleton (sumCofan sumCofan_inl_sumIso_hom sumCofan_inr_sumIso_hom)
open Paper.Extension.Singleton.Generation (Coordinates)

set_option backward.isDefEq.respectTransparency false in
private theorem reply_comparison :
    ((Coordinates.ofModel J M).sumIso Uty Uty).inv =
      (Kleisli.Type.coprodIsoSum Tree ((J).obj ((M).obj Uty)) ((J).obj ((M).obj Uty))).hom := by
  let comparison := asIso (coprodComparison (J) ((M).obj Uty) ((M).obj Uty))
  let typeSum := Types.binaryCoproductIso ((M).obj Uty) ((M).obj Uty)
  have decode : ((M).coprodIso Uty Uty).inv = typeSum.hom := by
    change typeSum.hom ≫ 𝟙 _ = typeSum.hom
    rw [Category.comp_id]
  change comparison.hom ≫ (J).map ((M).coprodIso Uty Uty).inv = _
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
theorem reply_tags :
    ((F).map (sumCofan Seed Uty Uty).inl).of PUnit.unit = (pure (replyValue false) : Tree _) ∧
      ((F).map (sumCofan Seed Uty Uty).inr).of PUnit.unit = (pure (replyValue true) : Tree _) := by
  let := regionTypingCoherent raw compatible
  have h := Paper.Extension.Singleton.denoteFunctor_preserves (Φ := Op) J M (fun _ _ => ⟨rfl, rfl⟩)
    (Paper.WithPairReturns.joined_seedDenotes (Φ := Op) J M (fun _ _ => ⟨rfl, rfl⟩) false)
  have hl := h.inl Uty Uty
  have hr := h.inr Uty Uty
  change 𝟙 _ ≫ (F).map (sumCofan Seed Uty Uty).inl ≫ 𝟙 _ = _ at hl
  change 𝟙 _ ≫ (F).map (sumCofan Seed Uty Uty).inr ≫ 𝟙 _ = _ at hr
  rw [Category.comp_id, Category.id_comp, reply_comparison, Kleisli.Type.inl_coprodIsoSum_hom] at hl
  rw [Category.comp_id, Category.id_comp, reply_comparison, Kleisli.Type.inr_coprodIsoSum_hom] at hr
  exact ⟨congrArg (fun f => f.of PUnit.unit) hl, congrArg (fun f => f.of PUnit.unit) hr⟩

set_option backward.isDefEq.respectTransparency false in
private theorem route_reply {A : Ty Atom} (a b : Uobj ⟶ Obj A) (reply : Bool) :
    ((F).map (replyIso.hom ≫ coprod.desc a b)).of (replyValue reply) =
      ((F).map (if reply then b else a)).of PUnit.unit := by
  have left : (sumCofan Seed Uty Uty).inl ≫ replyIso.hom ≫ coprod.desc a b = a := by
    rw [← Category.assoc, sumCofan_inl_sumIso_hom, coprod.inl_desc]
  have right : (sumCofan Seed Uty Uty).inr ≫ replyIso.hom ≫ coprod.desc a b = b := by
    rw [← Category.assoc, sumCofan_inr_sumIso_hom, coprod.inr_desc]
  cases reply
  · have h := congrArg (fun g : Uobj ⟶ Obj A => ((F).map g).of PUnit.unit) left
    rw [(F).map_comp, Kleisli.Type.comp_of_eq_kleisliRight] at h
    change (Bind.bind (m := Tree) (((F).map (sumCofan Seed Uty Uty).inl).of PUnit.unit)
      (fun x => ((F).map (replyIso.hom ≫ coprod.desc a b)).of x) : Tree (Ty.denote Atoms A)) = _ at h
    rw [reply_tags.1, pure_bind] at h
    exact h
  · have h := congrArg (fun g : Uobj ⟶ Obj A => ((F).map g).of PUnit.unit) right
    rw [(F).map_comp, Kleisli.Type.comp_of_eq_kleisliRight] at h
    change (Bind.bind (m := Tree) (((F).map (sumCofan Seed Uty Uty).inr).of PUnit.unit)
      (fun x => ((F).map (replyIso.hom ≫ coprod.desc a b)).of x) : Tree (Ty.denote Atoms A)) = _ at h
    rw [reply_tags.2, pure_bind] at h
    exact h

set_option backward.isDefEq.respectTransparency false in
theorem choose_copair_tree {A : Ty Atom} (a b : Uobj ⟶ Obj A) :
    ((F).map (choose ≫ replyIso.hom ≫ coprod.desc a b)).of PUnit.unit =
      vis .poll (fun r : Bool => ((F).map (if r then b else a : Uobj ⟶ Obj A)).of PUnit.unit) := by
  rw [(F).map_comp, Kleisli.Type.comp_of_eq_kleisliRight]
  change ((((F).map choose).of PUnit.unit >>= fun x => ((F).map
    (replyIso.hom ≫ coprod.desc a b)).of x) : Tree (Ty.denote Atoms A)) = _
  rw [choose_image, vis_bind]
  apply congrArg (vis Event.poll)
  funext r
  rw [pure_bind, route_reply]

set_option backward.isDefEq.respectTransparency false in
private theorem feedback_choose {enter next : Uobj ⟶ Three}
    (edge : enter ≫ mixedSourceStep = choose ≫ replyIso.hom ≫
      coprod.desc (enter ≫ (coprod.inr : Three ⟶ Uobj ⨿ Three)) (next ≫ coprod.inr)) :
    out (runMixed enter) = Part.some (.vis Event.poll (fun b => if b then runMixed next else runMixed enter)) := by
  let result := iterateChosen Seed mixedSourceStep
  have step : enter ≫ result = choose ≫ replyIso.hom ≫
      coprod.desc (enter ≫ result) (next ≫ result) := calc
    enter ≫ result = enter ≫ mixedSourceStep ≫ coprod.desc (𝟙 Uobj) result :=
      congrArg (enter ≫ ·) (iterateChosen_fixpoint Seed mixedSourceStep)
    _ = _ := by
      rw [← Category.assoc enter, edge]
      simp only [Category.assoc, coprod.desc_comp, coprod.inr_desc]
  change out (((F).map (enter ≫ result)).of PUnit.unit : Tree PUnit.{2}) = _
  rw [step, choose_copair_tree, out_vis]
  apply congrArg Part.some
  apply congrArg (Silmaril.Elgot.ITree.Visible.vis Event.poll)
  funext b
  cases b <;> rfl

theorem mixed_visible :
    out (runMixed firstMode) = Part.some (.vis Event.poll (fun b =>
      if b then runMixed secondMode else runMixed firstMode)) ∧
    out (runMixed secondMode) = Part.some (.vis Event.poll (fun b =>
      if b then runMixed firstMode else runMixed secondMode)) :=
  ⟨feedback_choose mixed_first_edge, feedback_choose mixed_second_edge⟩

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CyclicFoldVisible
