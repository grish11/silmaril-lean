module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetOperandExample

/-! # Native replay on a cyclic square that forgets a tag -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.OperandExample

open CategoryTheory CategoryTheory.Limits
open EntryLetObstruction
open Paper.TypeCategory (ofRegion discardArrow sumIso)
open Extension.Singleton (projection projectStep iterateChosen)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local notation "J" => projection Seed

/-- Forgetting either recurrent tag leaves the same computation on Unit. -/
theorem taggedSource_forget (q : X ⟶ X) :
    taggedSource q ≫ coprod.map (𝟙 X) forget = forget ≫ q ≫ discardArrow U ≫ coprod.inr :=
  EntryLetOperandExample.taggedSource_forget q

theorem movedTarget_eq :
    ofRegion movedStep_typed ≫ (sumIso U U).hom =
      ofRegion movedRequest_typed ≫ discardArrow U ≫ coprod.inr :=
  EntryLetOperandExample.movedTarget_eq

theorem flatTarget_eq :
    ofRegion flatStep_typed ≫ (sumIso U U).hom =
      ofRegion flatRequest_typed ≫ discardArrow U ≫ coprod.inr :=
  EntryLetOperandExample.flatTarget_eq

/-- Moving the request at the flat table root keeps its recurrent output. -/
theorem move_recurring_request : Site.here.move flatRecurringRequest = some movedRecurringRequest :=
  EntryLetOperandExample.move_recurring_request

/-- Forgetting the tag is a structural constructor return. -/
theorem forget_structural : Extension.Singleton.StructuralValues.HomProperty Seed ((J).map forget) :=
  Extension.Singleton.StructuralValues.branch_mem Seed .unit

/-- The two tags remain distinct in the corrected quotient, so the state
map has no retraction of the kind required by split-image uniformity. -/
theorem no_retraction : ¬ ∃ k : (J).obj X ⟶ (J).obj D, (J).map forget ≫ k = 𝟙 ((J).obj D) :=
  EntryLetOperandExample.no_retraction

/-- The diagnostic separates the two written composites in standard Paper. -/
theorem native_square_ne :
    source ≫ coprod.map (𝟙 X) forget ≠ forget ≫ target :=
  EntryLetOperandExample.native_square_ne

/-- Pull the entry-let move back through the substitution of Unit and
replace the target representative to obtain a standard Paper square. -/
theorem repaired :
    ∃ g : X ⟶ X ⨿ X, projectStep Seed g = projectStep Seed target ∧
      source ≫ coprod.map (𝟙 X) forget = forget ≫ g :=
  EntryLetOperandExample.repaired

theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((J).obj X)) ((J).map forget) =
      (J).map forget ≫ projectStep Seed target :=
  EntryLetOperandExample.corrected_square

theorem corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed target) :=
  EntryLetOperandExample.corrected_iterate

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.OperandExample
