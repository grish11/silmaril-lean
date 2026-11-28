module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ReplayExample

/-! # Cyclic binary representative repair -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.ReplayExample

open CategoryTheory CategoryTheory.Limits
open Paper.EntryLetObstruction.Destructure (U)
open Paper.WithEntryLet.OperandExample (X D)
open Paper.TypeCategory (ofRegion discardArrow sumIso)
open Extension.Singleton (projection projectStep iterateChosen)
open SequencingObstruction (Instruction)

local notation "Proj" => projection Seed
local notation "Unary" => Paper.WithEntryLet.Step (τ := Ty Empty) (Φ := Instruction)

/-- The repaired target's written step performs the request and repeats. -/
theorem movedTarget_eq :
    ofRegion movedStep_typed ≫ (sumIso U U).hom =
      ofRegion moved_typed ≫ discardArrow U ≫ coprod.inr :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ReplayExample.movedTarget_eq

/-- The two tags remain distinct after projection, but the state map
sends both to Unit. -/
theorem no_retraction :
    ¬ ∃ k : (Proj).obj X ⟶ (Proj).obj D, (Proj).map forget ≫ k = 𝟙 ((Proj).obj D) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ReplayExample.no_retraction

/-- The written square still fails after adjoining unary entry-let. -/
theorem unary_square_ne :
    projectStep Unary source ≫ coprod.map (𝟙 ((projection Unary).obj X)) ((projection Unary).map forget) ≠
      (projection Unary).map forget ≫ projectStep Unary target :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ReplayExample.unary_square_ne

theorem native_square_ne :
    source ≫ coprod.map (𝟙 X) forget ≠ forget ≫ target :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ReplayExample.native_square_ne

/-- A single binary move supplies a representative of the same η class
with a standard Paper square. -/
theorem repaired :
    ∃ g : X ⟶ X ⨿ X, projectStep Seed g = projectStep Seed target ∧
      source ≫ coprod.map (𝟙 X) forget = forget ≫ g :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ReplayExample.repaired

theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((Proj).obj X)) ((Proj).map forget) =
      (Proj).map forget ≫ projectStep Seed target :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ReplayExample.corrected_square

/-- The addressed binary repair enables a standard Paper replay of the
cyclic square before projecting the iteration equation. -/
theorem corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (Proj).map forget ≫ iterateChosen Seed (projectStep Seed target) :=
  Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.ReplayExample.corrected_iterate

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.ReplayExample
