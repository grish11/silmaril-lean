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

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CyclicFoldVisible
