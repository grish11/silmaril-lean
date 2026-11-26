module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.CyclicFoldVisible

/-! # A guarded, visible regression for the exact structural fold -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible

open CategoryTheory CategoryTheory.Limits Silmaril.Elgot.ITree
open Extension.Singleton (iterateChosen)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local notation "fold" => foldState Seed UnitTy

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

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithPairReturns.StructuralValues.Uniformity.Cyclic.Visible
