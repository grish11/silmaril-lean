module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithBoundEntryEta.Replay.Square.Example.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta.SquareReplayExample

/-! # Two representative changes in a cyclic corrected square -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.SquareReplay.Example

open CategoryTheory CategoryTheory.Limits
open WithEntryLet.OperandExample (X forget)
open EntryLetObstruction (U)
open Paper.TypeCategory (ofRegion sumCofan sumIso)
open Extension.Singleton (projectStep projection iterateChosen)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.WithBoundEntryEta

local notation "J" => projection Seed

/-- The original composites differ in standard Paper before changing representatives. -/
theorem native_square_ne : source ≫ coprod.map (𝟙 X) forget ≠ forget ≫ target :=
  SquareReplayExample.native_square_ne

theorem repaired :
    ∃ g : X ⟶ X ⨿ X,
      projectStep Seed movedSource = projectStep Seed source ∧ projectStep Seed g = projectStep Seed target ∧
      movedSource ≫ coprod.map (𝟙 X) forget = forget ≫ g :=
  SquareReplayExample.repaired

theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((J).obj X)) ((J).map forget) =
      (J).map forget ≫ projectStep Seed target :=
  SquareReplayExample.corrected_square

theorem corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed target) :=
  SquareReplayExample.corrected_iterate

/-- The exact left and right transitions return opposite recurrent tags. -/
theorem alternating_routes (round : X ⟶ X) :
    (sumCofan U U).inl ≫ alternating round =
      (sumCofan U U).inl ≫ forget ≫ round ≫ (sumCofan U U).inr ≫ coprod.inr ∧
    (sumCofan U U).inr ≫ alternating round =
      (sumCofan U U).inr ≫ forget ≫ round ≫ (sumCofan U U).inl ≫ coprod.inr :=
  SquareReplayExample.alternating_routes round

/-- The same guarded round now gives a native square with alternating tags. -/
theorem alternating_native_square :
    alternating (ofRegion movedWorkTyped) ≫ coprod.map (𝟙 X) forget =
      forget ≫ (ofRegion flatTyped ≫ (sumIso U U).hom) :=
  SquareReplayExample.alternating_native_square

/-- Replacing the common round in both arms and reusing the flat target
preserves the corrected steps. Native uniformity applies to those representatives. -/
theorem alternating_corrected_iterate :
    iterateChosen Seed (projectStep Seed (alternating (ofRegion workTyped))) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed target) :=
  SquareReplayExample.alternating_corrected_iterate

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithBoundEntryEta.SquareReplay.Example
