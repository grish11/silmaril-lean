module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithEntryLet.Replay.Operand.Example.Defs

/-! # Two successive entry-let moves with the same tag-forgetting state map -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.ChainExample

open CategoryTheory CategoryTheory.Limits
open EntryLetObstruction OperandExample
open Silmaril.DeBruijn (lift)
open SequencingObstruction (Instruction)
open Paper.TypeCategory (ofRegion)

def sites : List Site := [.entry .here, .block 0 .here]

/-- Both tags execute two requests and recur with their original tag. -/
noncomputable def source : D ⟶ X ⨿ D :=
  taggedSource (ofRegion movedRequest_typed ≫ ofRegion movedRequest_typed)

/-- A native let expansion that mentions the source's discarded input. -/
def expandedFirstMove : Region Instruction :=
  .let₁ (.var 0) ((firstRequestMoved.substVars (Tm.singleSubst .unit ∘ lift Nat.succ)).renameVars Nat.succ)

/-- The written end of the mixed derivation keeps the expanded let. -/
def expandedBothMoves : Region Instruction :=
  .let₁ (.var 0) ((bothRequestsMoved.substVars (Tm.singleSubst .unit ∘ lift Nat.succ)).renameVars Nat.succ)

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithEntryLet.ChainExample
