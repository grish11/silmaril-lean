module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Chain.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Example.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.EntryLetChainExample

/-! # A two-move cyclic square and a mixed-step boundary -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.ChainExample

open CategoryTheory CategoryTheory.Limits
open Silmaril.DeBruijn (lift)
open EntryLetObstruction
open OperandExample (Bit D X Seed forget flatStep_typed)
open Paper.TypeCategory (ofRegion sumIso)
open Extension.Singleton (projection projectStep iterateChosen projectSquare_iff)
open SequencingObstruction (Instruction)
open Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper

local notation "J" => projection Seed
local notation "θ" => (Tm.singleSubst (Tm.unit : Tm Instruction) ∘ lift Nat.succ)

theorem target_typed : ValueBranches [U] twoFlatRequests [Bit] :=
  EntryLetChainExample.sequenceRequests_typed flatRequest_typed flatStep_typed

noncomputable def target : X ⟶ X ⨿ X := ofRegion target_typed ≫ (sumIso U U).hom

/-- Both addressed moves replay in the constructor-precomposed target. -/
theorem moves_composite :
    Site.moveAll sites (twoFlatRequests.substVars θ) = some (bothRequestsMoved.substVars θ) :=
  EntryLetChainExample.moves_composite

/-- Leaving either request inside its flat table gives a different native square. -/
theorem unfinished_square_ne {r : Region Instruction} (hr : ValueBranches [U] r [Bit])
    (h : r = twoFlatRequests ∨ r = firstRequestMoved ∨ r = secondRequestMoved) :
    source ≫ coprod.map (𝟙 X) forget ≠ forget ≫ (ofRegion hr ≫ (sumIso U U).hom) :=
  EntryLetChainExample.unfinished_square_ne hr h

/-- No single addressed move on this written composite can give the native square. -/
theorem no_single_move_repairs (site : Site) {r : Region Instruction}
    (hr : ValueBranches [Bit] r [Bit])
    (hm : site.move (twoFlatRequests.substVars θ) = some r) :
    source ≫ coprod.map (𝟙 X) forget ≠ ofRegion hr ≫ (sumIso U U).hom :=
  EntryLetChainExample.no_single_move_repairs site hr hm

/-- The two moves yield a replacement in the corrected class and a native square. -/
theorem repaired :
    ∃ g : X ⟶ X ⨿ X, projectStep Seed g = projectStep Seed target ∧
      source ≫ coprod.map (𝟙 X) forget = forget ≫ g :=
  EntryLetChainExample.repaired

theorem corrected_square :
    projectStep Seed source ≫ coprod.map (𝟙 ((J).obj X)) ((J).map forget) =
      (J).map forget ≫ projectStep Seed target := by
  obtain ⟨g, hg, native⟩ := repaired
  rw [← hg]
  exact (projectSquare_iff Seed source g forget).2 (congrArg ((J).map) native)

/-- Replay gives uniformity for the same state map as `OperandExample.no_retraction`. -/
theorem corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed target) :=
  EntryLetChainExample.corrected_iterate

/-- A native let expansion between the two moves reads the discarded
input, so the intermediate region is outside the literal substitution
image. The second EntryLet move still succeeds under the new binder. -/
theorem mixed_expansion :
      Paper.Eqv [Bit] (firstRequestMoved.substVars θ) expandedFirstMove [Bit] ∧
      (∀ q : Region Instruction, q.substVars θ ≠ expandedFirstMove) ∧
      (Site.unaryBody (.block 0 .here)).move expandedFirstMove =
        some (.let₁ (.var 0) ((bothRequestsMoved.substVars θ).renameVars Nat.succ)) :=
  EntryLetChainExample.mixed_expansion

theorem expandedBothMoves_typed : ValueBranches [Bit] expandedBothMoves [Bit] :=
  EntryLetChainExample.expandedBothMoves_typed

/-- The intermediate can leave the substitution image while the result
still has a standard-Paper-equivalent representative in that image. -/
theorem mixed_endpoint :
    Paper.Eqv [Bit] expandedBothMoves (bothRequestsMoved.substVars θ) [Bit] :=
  EntryLetChainExample.mixed_endpoint

/-- The native endpoint equality holds with the let still expanded. -/
theorem mixed_final_composite :
    source ≫ coprod.map (𝟙 X) forget = ofRegion expandedBothMoves_typed ≫ (sumIso U U).hom :=
  EntryLetChainExample.mixed_final_composite

/-- Replay the entry move, the native expansion, and the move under the
new binder to recover the original cyclic square in standard Paper. -/
theorem mixed_repaired :
    ∃ g : X ⟶ X ⨿ X, projectStep Seed g = projectStep Seed target ∧
      source ≫ coprod.map (𝟙 X) forget = forget ≫ g :=
  EntryLetChainExample.mixed_repaired

/-- Ordinary constructor uniformity applies to the repaired mixed square. -/
theorem mixed_corrected_iterate :
    iterateChosen Seed (projectStep Seed source) =
      (J).map forget ≫ iterateChosen Seed (projectStep Seed target) :=
  EntryLetChainExample.mixed_corrected_iterate

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.ChainExample
