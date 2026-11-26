module

import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Doubling.Switching.OneSided.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Category.Singleton.Iteration.Doubling.Switching.Example.Thms

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.SwitchingExample

open CategoryTheory CategoryTheory.Limits

private abbrev LeftState := Silmaril.coprod Flag U
private abbrev Regrouped := Silmaril.coprod LeftState U

private noncomputable abbrev enterFlag : FlagObj ⟶ Obj LeftState := (sumCofan Flag U).inl
private noncomputable abbrev enterBack : UnitObj ⟶ Obj LeftState := (sumCofan Flag U).inr
private noncomputable abbrev enterLeft : Obj LeftState ⟶ Obj Regrouped := (sumCofan LeftState U).inl
private noncomputable abbrev enterRight : UnitObj ⟶ Obj Regrouped := (sumCofan LeftState U).inr

private noncomputable def pack : Obj Regrouped ⟶ StateObj :=
  blockCopair (blockCopair stateLeft (flagRight ≫ stateRight)) (flagLeft ≫ stateRight)

private noncomputable def unpackState : StateObj ⟶ Obj Regrouped :=
  blockCopair (enterFlag ≫ enterLeft) (blockCopair enterRight (enterBack ≫ enterLeft))

set_option backward.isDefEq.respectTransparency false

@[reassoc] private theorem regroup_flag : enterFlag ≫ enterLeft ≫ pack = stateLeft := by
  unfold pack enterFlag enterLeft
  rw [inl_blockCopair, inl_blockCopair]

@[reassoc] private theorem regroup_back : enterBack ≫ enterLeft ≫ pack = flagRight ≫ stateRight := by
  unfold pack enterBack enterLeft
  rw [inl_blockCopair, inr_blockCopair]

@[reassoc] private theorem regroup_right : enterRight ≫ pack = flagLeft ≫ stateRight := by
  unfold pack enterRight
  rw [inr_blockCopair]

private noncomputable def regroup : Obj Regrouped ≅ StateObj where
  hom := pack
  inv := unpackState
  hom_inv_id := by
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit LeftState U)
    · apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit Flag U)
      · change enterFlag ≫ enterLeft ≫ pack ≫ unpackState = enterFlag ≫ enterLeft ≫ 𝟙 _
        rw [regroup_flag_assoc, Category.comp_id]
        exact inl_blockCopair _ _
      · change enterBack ≫ enterLeft ≫ pack ≫ unpackState = enterBack ≫ enterLeft ≫ 𝟙 _
        rw [regroup_back_assoc, Category.comp_id]
        unfold unpackState stateRight flagRight
        rw [inr_blockCopair, inr_blockCopair]
    · change enterRight ≫ pack ≫ unpackState = enterRight ≫ 𝟙 _
      rw [← Category.assoc, regroup_right, Category.comp_id]
      unfold unpackState stateRight flagLeft
      rw [Category.assoc, inr_blockCopair, inl_blockCopair]
  inv_hom_id := by
    apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit Flag Flag)
    · change stateLeft ≫ unpackState ≫ pack = stateLeft ≫ 𝟙 _
      unfold unpackState stateLeft
      rw [← Category.assoc, inl_blockCopair, Category.comp_id]
      simpa only [Category.assoc] using regroup_flag
    · apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit U U)
      · change flagLeft ≫ stateRight ≫ unpackState ≫ pack = flagLeft ≫ stateRight ≫ 𝟙 _
        unfold unpackState stateRight flagLeft
        rw [← Category.assoc (sumCofan Flag Flag).inr, inr_blockCopair, ← Category.assoc,
          inl_blockCopair, Category.comp_id]
        exact regroup_right
      · change flagRight ≫ stateRight ≫ unpackState ≫ pack = flagRight ≫ stateRight ≫ 𝟙 _
        unfold unpackState stateRight flagRight
        rw [← Category.assoc (sumCofan Flag Flag).inr, inr_blockCopair, ← Category.assoc,
          inr_blockCopair, Category.comp_id]
        simpa only [Category.assoc] using regroup_back

local notation "Ports" => (AnswerObj ⨿ Obj LeftState) ⨿ UnitObj

private noncomputable def mixedLeft : Obj LeftState ⟶ Ports :=
  blockCopair
    (blockCopair
      (ofRegion earlyTyped ≫ coprod.inl ≫ coprod.inl)
      (ofRegion (requestTyped .first) ≫ coprod.inr))
    (ofRegion (requestTyped .second) ≫ flagRight ≫ enterFlag ≫ coprod.inr ≫ coprod.inl)

private noncomputable def exitEffect : UnitObj ⟶ AnswerObj :=
  ofRegion (τ := Ty Empty) (Φ := Op) (A := U) (B := Answer) secondExitTyped

private noncomputable def exitRight : UnitObj ⟶ AnswerObj ⨿ Obj LeftState :=
  exitEffect ≫ coprod.inl

private noncomputable abbrev mixedStep : Obj Regrouped ⟶ AnswerObj ⨿ Obj Regrouped :=
  OneSidedSwitch.step mixedLeft exitRight

/-- The actual one-sided step has both left and right transfers from its
left row. This square checks all four input modes in the native quotient. -/
private theorem regroup_square :
    mixedStep ≫ coprod.map (𝟙 AnswerObj) regroup.hom = regroup.hom ≫ step := by
  let join := joinBlockExits LeftState U AnswerObj
  have mixed_enter : enterLeft ≫ mixedStep = mixedLeft ≫ join := by
    change enterLeft ≫ (blockCopair mixedLeft (exitRight ≫ coprod.inl) ≫ join) = _
    rw [← Category.assoc, show enterLeft ≫ blockCopair mixedLeft (exitRight ≫ coprod.inl) =
      mixedLeft from inl_blockCopair _ _]
  have exit_enter : enterRight ≫ mixedStep = exitRight ≫ coprod.inl ≫ join := by
    change enterRight ≫ (blockCopair mixedLeft (exitRight ≫ coprod.inl) ≫ join) = _
    rw [← Category.assoc, show enterRight ≫ blockCopair mixedLeft (exitRight ≫ coprod.inl) =
      exitRight ≫ coprod.inl from inr_blockCopair _ _, Category.assoc]
  let send := coprod.map (𝟙 AnswerObj) pack
  have send_exit : (coprod.inl : AnswerObj ⟶ AnswerObj ⨿ Obj LeftState) ≫ coprod.inl ≫ join ≫ send =
      (coprod.inl : AnswerObj ⟶ AnswerObj ⨿ StateObj) := by
    unfold join joinBlockExits send
    simp only [coprod.inl_desc_assoc, coprod.inl_map_assoc, Category.id_comp, coprod.inl_map]
  have send_back : (coprod.inr : Obj LeftState ⟶ AnswerObj ⨿ Obj LeftState) ≫ coprod.inl ≫ join ≫ send =
      enterLeft ≫ pack ≫ coprod.inr := by
    unfold join joinBlockExits send
    simp only [coprod.inl_desc_assoc, coprod.inr_map_assoc, coprod.inr_map]
  have send_right : (coprod.inr : UnitObj ⟶ Ports) ≫ join ≫ send = flagLeft ≫ stateRight ≫ coprod.inr := by
    unfold join joinBlockExits send
    rw [coprod.inr_desc_assoc, Category.assoc, coprod.inr_map, regroup_right_assoc]
  have old_left : stateLeft ≫ step = left ≫ coprod.map (𝟙 AnswerObj) stateRight := inl_blockCopair _ _
  have old_right : stateRight ≫ step = right ≫ coprod.map (𝟙 AnswerObj) stateLeft := inr_blockCopair _ _
  have early_original : flagLeft ≫ left = ofRegion earlyTyped ≫ coprod.inl := by
    unfold left
    rw [← Category.assoc flagLeft,
      show flagLeft ≫ (sumIso U U).hom = coprod.inl from sumCofan_inl_sumIso_hom _ _, coprod.inl_desc]
  have first_original : flagRight ≫ left = ofRegion (requestTyped .first) ≫ flagLeft ≫ coprod.inr := by
    unfold left
    rw [← Category.assoc flagRight,
      show flagRight ≫ (sumIso U U).hom = coprod.inr from sumCofan_inr_sumIso_hom _ _, coprod.inr_desc]
  have second_original : flagLeft ≫ right = exitEffect ≫ coprod.inl := by
    unfold right
    rw [← Category.assoc flagLeft,
      show flagLeft ≫ (sumIso U U).hom = coprod.inl from sumCofan_inl_sumIso_hom _ _, coprod.inl_desc]
    rfl
  have flag_mixed : enterFlag ≫ mixedLeft = blockCopair
      (ofRegion earlyTyped ≫ coprod.inl ≫ coprod.inl)
      (ofRegion (requestTyped .first) ≫ coprod.inr) := inl_blockCopair _ _
  have early_mixed : flagLeft ≫ enterFlag ≫ mixedLeft =
      ofRegion earlyTyped ≫ coprod.inl ≫ coprod.inl := by
    rw [flag_mixed]
    exact inl_blockCopair _ _
  have first_mixed : flagRight ≫ enterFlag ≫ mixedLeft = ofRegion (requestTyped .first) ≫ coprod.inr := by
    rw [flag_mixed]
    exact inr_blockCopair _ _
  have back_mixed : enterBack ≫ mixedLeft =
      ofRegion (requestTyped .second) ≫ flagRight ≫ enterFlag ≫ coprod.inr ≫ coprod.inl :=
    inr_blockCopair _ _
  have enter_send : enterLeft ≫ mixedStep ≫ send = mixedLeft ≫ join ≫ send := by
    rw [← Category.assoc enterLeft, mixed_enter, Category.assoc]
  change mixedStep ≫ send = pack ≫ step
  apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit LeftState U)
  · apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit Flag U)
    · apply BinaryCofan.IsColimit.hom_ext (sumCofanIsColimit U U)
      · change flagLeft ≫ enterFlag ≫ enterLeft ≫ mixedStep ≫ send =
          flagLeft ≫ enterFlag ≫ enterLeft ≫ pack ≫ step
        rw [enter_send, regroup_flag_assoc, old_left, ← Category.assoc enterFlag mixedLeft,
          ← Category.assoc flagLeft, early_mixed, ← Category.assoc flagLeft left, early_original]
        simp only [Category.assoc, send_exit, coprod.inl_map, Category.id_comp]
      · change flagRight ≫ enterFlag ≫ enterLeft ≫ mixedStep ≫ send =
          flagRight ≫ enterFlag ≫ enterLeft ≫ pack ≫ step
        rw [enter_send, regroup_flag_assoc, old_left, ← Category.assoc enterFlag mixedLeft,
          ← Category.assoc flagRight, first_mixed, ← Category.assoc flagRight left, first_original]
        simp only [Category.assoc, send_right, coprod.inr_map]
    · change enterBack ≫ enterLeft ≫ mixedStep ≫ send = enterBack ≫ enterLeft ≫ pack ≫ step
      rw [enter_send, regroup_back_assoc, old_right, ← Category.assoc flagRight right, right_repeat,
        ← Category.assoc enterBack mixedLeft, back_mixed]
      simp only [Category.assoc, send_back, regroup_flag_assoc, coprod.inr_map]
  · change enterRight ≫ mixedStep ≫ send = enterRight ≫ pack ≫ step
    rw [← Category.assoc enterRight mixedStep, exit_enter, regroup_right_assoc,
      old_right, ← Category.assoc flagLeft right, second_original]
    simp only [exitRight, Category.assoc, send_exit, coprod.inl_map, Category.id_comp]

private theorem mixed_iterates : iterate (mixedStep ≫ coprod.desc coprod.inl mixedStep) = iterate mixedStep :=
  OneSidedSwitch.iterate_double_of_regrouping mixedStep step regroup regroup_square iterates_agree

/-- Both native iterates recover the existing written outcome, which has
ordered Unit/product exits and observes `first` before `second` on its
two-leg path. -/
example :
    enterFlag ≫ enterLeft ≫ iterate (mixedStep ≫ coprod.desc coprod.inl mixedStep) = ofRegion outcomeTyped ∧
    enterFlag ≫ enterLeft ≫ iterate mixedStep = ofRegion outcomeTyped := by
  have outcome : enterFlag ≫ enterLeft ≫ iterate mixedStep = ofRegion outcomeTyped := by
    rw [OneSidedSwitch.iterate_regrouping mixedStep step regroup regroup_square]
    change enterFlag ≫ enterLeft ≫ pack ≫ iterate step = _
    rw [regroup_flag_assoc]
    exact left_iterates.2
  exact ⟨mixed_iterates.symm ▸ outcome, outcome⟩

end Silmaril.Isotope.LambdaSSA.Region.Paper.TypeCategory.SwitchingExample
