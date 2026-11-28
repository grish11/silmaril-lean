module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.StructuralValues.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetReplayExample

/-! # Corrected iteration despite failure of fixed native square reflection -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.ReplayExample

open CategoryTheory CategoryTheory.Limits
open Extension.Singleton (projection projectStep iterateChosen)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

theorem embed_constructor : Paper.TypeCategory.ConstructorReturn embed :=
  EntryLetReplayExample.embed_constructor

theorem embed_structural :
    Extension.Singleton.StructuralValues.HomProperty Seed ((projection Seed).map embed) := by
  obtain ⟨_, ha, eq⟩ := embed_constructor
  rw [eq]
  exact Extension.Singleton.StructuralValues.branch_mem Seed ha

/-- With the written source, target, and state map, the corrected square
does not give the standard Paper square required by native replay. -/
theorem native_square_ne :
    source ≫ coprod.map (𝟙 X) embed ≠ embed ≫ target :=
  EntryLetReplayExample.native_square_ne

/-- The same three representatives satisfy the actual corrected square. -/
theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((projection Seed).obj X)) ((projection Seed).map embed) =
      (projection Seed).map embed ≫ projectStep Seed target :=
  EntryLetReplayExample.corrected_square

/-- A replacement target can recover a standard square in this example. -/
theorem native_square_repaired :
    ∃ g : D ⟶ X ⨿ D, projectStep Seed g = projectStep Seed target ∧
      source ≫ coprod.map (𝟙 X) embed = embed ≫ g :=
  EntryLetReplayExample.native_square_repaired

/-- Iteration comparison follows in the corrected quotient using the split
state inclusion and the target's recurrent image. -/
theorem corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (projection Seed).map embed ≫ iterateChosen Seed (projectStep Seed target) :=
  EntryLetReplayExample.corrected_iterate

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.ReplayExample
