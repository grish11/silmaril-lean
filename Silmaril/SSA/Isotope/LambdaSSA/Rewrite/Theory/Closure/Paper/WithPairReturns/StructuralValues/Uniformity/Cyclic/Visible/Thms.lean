module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CyclicFoldVisible

/-! # A guarded, visible regression for the exact structural fold -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot.ITree
open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Extension.Singleton (iterateChosen sumCofan)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local notation "fold" => foldState Seed UnitTy

/-- The exact reply injections return their typed values without an event. -/
theorem reply_tags_tree :
    (interpretation.map (sumCofan Seed UnitTy UnitTy).inl).of PUnit.unit =
      (pure (replyValue false) : Tree _) ∧
    (interpretation.map (sumCofan Seed UnitTy UnitTy).inr).of PUnit.unit =
      (pure (replyValue true) : Tree _) :=
  CyclicFoldVisible.reply_tags

/-- Poll once and interpret the selected continuation on its typed Unit payload. -/
theorem choose_copair_tree {A : Ty Atom} (a b : One ⟶ Obj A) :
    (interpretation.map (choose ≫ replyIso.hom ≫ coprod.desc a b)).of PUnit.unit =
      vis .poll (fun r : Bool => (interpretation.map (if r then b else a : One ⟶ Obj A)).of PUnit.unit) :=
  CyclicFoldVisible.choose_copair_tree a b

/-- The actual quotient square uses the fold with the same written syntax as the replay audit. -/
theorem square : sourceStep ≫ coprod.map (𝟙 One) fold = fold ≫ targetStep :=
  CyclicFoldVisible.square

/-- The two distinct states execute a poll and enter the other state. -/
theorem two_cycle :
    firstMode ≠ secondMode ∧
      firstMode ≫ sourceStep = poll ≫ secondMode ≫ (coprod.inr : Three ⟶ One ⨿ Three) ∧
      secondMode ≫ sourceStep = poll ≫ firstMode ≫ (coprod.inr : Three ⟶ One ⨿ Three) :=
  ⟨CyclicFoldVisible.modes_ne, CyclicFoldVisible.first_edge, CyclicFoldVisible.second_edge⟩

/-- The folded mode polls and enters itself. -/
theorem target_self_loop :
    foldedMode ≫ targetStep = poll ≫ foldedMode ≫ (coprod.inr : Two ⟶ One ⨿ Two) :=
  CyclicFoldVisible.target_edge

/-- Both cyclic modes map to the same polling self-loop. -/
theorem fold_modes : firstMode ≫ fold = foldedMode ∧ secondMode ≫ fold = foldedMode :=
  CyclicFoldVisible.fold_modes

/-- Folding the distinct cyclic modes makes the state map nonmonic. -/
theorem fold_not_mono : ¬ Mono fold :=
  CyclicFoldVisible.fold_not_mono

/-- The cyclic source and folded target have equal iterations along the fold in the quotient. -/
theorem iteration : iterateChosen Seed sourceStep = fold ≫ iterateChosen Seed targetStep :=
  CyclicFoldVisible.iteration

/-- On each back-edge the weak ITree exposes the poll and continues at the opposite mode for either reply. -/
theorem visible_cycle :
    out (runFrom firstMode) = Part.some (.vis Event.poll (fun _ => runFrom secondMode)) ∧
      out (runFrom secondMode) = Part.some (.vis Event.poll (fun _ => runFrom firstMode)) :=
  ⟨CyclicFoldVisible.first_visible, CyclicFoldVisible.second_visible⟩

/-- Replies can select either recursive copy, and the actual quotient square still commutes. -/
theorem mixed_square :
    mixedSourceStep ≫ coprod.map (𝟙 One) fold = fold ≫ mixedTargetStep :=
  CyclicFoldVisible.mixed_square

/-- Folding the reply-dependent cycle preserves guarded iteration in the ordered-pair quotient. -/
theorem mixed_iteration :
    iterateChosen Seed mixedSourceStep = fold ≫ iterateChosen Seed mixedTargetStep :=
  CyclicFoldVisible.mixed_iteration

/-- The two mode arrows are distinct, and each orders its reply branches as self then switch. -/
theorem mixed_edges :
    firstMode ≠ secondMode ∧
    firstMode ≫ mixedSourceStep = choose ≫ replyIso.hom ≫
      coprod.desc (firstMode ≫ (coprod.inr : Three ⟶ One ⨿ Three)) (secondMode ≫ coprod.inr) ∧
    secondMode ≫ mixedSourceStep = choose ≫ replyIso.hom ≫
      coprod.desc (secondMode ≫ (coprod.inr : Three ⟶ One ⨿ Three)) (firstMode ≫ coprod.inr) :=
  ⟨CyclicFoldVisible.modes_ne, CyclicFoldVisible.mixed_first_edge, CyclicFoldVisible.mixed_second_edge⟩

/-- In either copy, the typed Boolean reply selects self on false and switch on true. -/
theorem mixed_visible :
    out (runMixed firstMode) = Part.some (.vis Event.poll (fun b =>
      if b then runMixed secondMode else runMixed firstMode)) ∧
    out (runMixed secondMode) = Part.some (.vis Event.poll (fun b =>
      if b then runMixed firstMode else runMixed secondMode)) :=
  CyclicFoldVisible.mixed_visible

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible
