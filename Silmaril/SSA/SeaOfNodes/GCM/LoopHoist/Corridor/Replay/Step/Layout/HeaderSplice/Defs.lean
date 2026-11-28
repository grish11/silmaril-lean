module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.CrossBlock.Defs

/-! # Adjacent placement on the current saved-layout CFG -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Block)
open Loop.MLIR.CF (TargetOp)
open AfterReorder.Second (intermediateBlocks savedHeader targetDecEqWith)

variable {Input extra : List Width} {saved carried result : Width}

abbrev HeaderBlock (Input : List Width) (saved carried result : Width) (extra : List Width) :=
  Block TargetOp (Label saved carried result extra) (((extra ++ [saved]) ++ [carried]) ++ Input) [result]

/-- Keep the layout, entry and exit; replace the shared header and update its origin order. -/
def install (state : Layout.State Input saved carried result extra)
    (header : HeaderBlock Input saved carried result extra) (request : Nomination) (index : Nat) :
    Layout.State Input saved carried result extra :=
  let cfg := state.reference.cfg
  let block : ∀ {args}, Label saved carried result extra args →
      Block TargetOp (Label saved carried result extra) (args ++ Input) [result]
    | _, .header => header
    | _, .exit => cfg.block .exit
  let origins := Header.Sequence.relocate ⟨index, request.cut⟩ request.origin state.reference.origins
  { state with reference := { state.reference with cfg := { cfg with block }, origins } }

structure Move (state : Layout.State Input saved carried result extra) where
  request : Nomination
  binding : CrossBlock.Kept (Label saved carried result extra)
  header : HeaderBlock Input saved carried result extra

def Move.next {state : Layout.State Input saved carried result extra} (move : Move state) :
    Layout.State Input saved carried result extra :=
  install state move.header move.request move.binding.index

def Move.cut {state : Layout.State Input saved carried result extra} (move : Move state) :
    Point (Label saved carried result extra) :=
  ⟨savedHeader, move.request.cut⟩

def Move.insertion {state : Layout.State Input saved carried result extra} (move : Move state) : Nat :=
  Header.afterRemoval move.binding.index move.request.cut

/-- Compare complete operand and use sites, retaining each source, slot and argument. -/
def sameSites {Labels : List Width → Type} [DecidableEq (Target Labels)]
    (a b : CrossBlock.HeaderSites Labels) : Bool :=
  decide (a.operands.map point = b.operands.map point ∧ a.uses.map occurrence = b.uses.map occurrence)
where
  point (p : Point Labels) := (p.block, p.cut)
  occurrence : Use Labels → (BlockId Labels × Nat) ⊕ (BlockId Labels × EdgeSlot × Nat)
    | .ordinary read => .inl (point read)
    | .phi source slot argument => .inr (source, slot, argument)

/-- Recheck the original destination, perform one typed swap, and resolve the
    moved origin's reads and uses at its translated position in the new header. -/
def emit? (state : Layout.State Input saved carried result extra) (request : Nomination) :
    Option (Move state) := do
  if !Layout.Discovery.supported? state then none else
    let binding ← CrossBlock.keep? state request.origin
    let insertion := Header.afterRemoval binding.index request.cut
    if insertion + 1 = binding.index ∨ binding.index + 1 = insertion then
      let _ := targetDecEqWith (saved := saved) (carried := carried) (result := result) (extra := extra)
      if GCM.Dominance.Placement.checkCut state.cfg intermediateBlocks binding.sites.operands
          binding.sites.uses ⟨savedHeader, request.cut⟩ then
        let header ← Header.Typed.swapAt? (min binding.index insertion) (state.cfg.block .header)
        let move : Move state := ⟨request, binding, header⟩
        let sites ← CrossBlock.findSites? move.next insertion 0 (Saved.origins (extra ++ [saved])) header
        if sameSites binding.sites sites then some move else none
      else none
    else none

structure Ranked (state : Layout.State Input saved carried result extra) where
  crossBlock : CrossBlock.Analysis state
  header : Option (Move state)

/-- Reuse the cross-block depth decision. If it stays in the header,
    a strictly later admitted cut wins the local tie. -/
def Ranked.laterHeader? {state : Layout.State Input saved carried result extra} (ranked : Ranked state) :
    Option (Move state) :=
  if ranked.crossBlock.selectedMove?.isSome then none
  else ranked.header.filter fun move => ranked.crossBlock.kept.point.cut < move.cut.cut

def Ranked.selection {state : Layout.State Input saved carried result extra} (ranked : Ranked state) :
    Point (Label saved carried result extra) × Layout.Output Input saved carried result :=
  match ranked.laterHeader? with
  | none => (ranked.crossBlock.point, ranked.crossBlock.output)
  | some move => (move.cut, ⟨extra, move.next⟩)

/-- Compare the unchanged cut with one nominated header cut and one nominated
    physical preheader cut for the same live origin. -/
def rank? (state : Layout.State Input saved carried result extra) (preheader : Nomination) (headerCut : Nat) :
    Option (Ranked state) := do
  let crossBlock ← CrossBlock.analyze? state preheader
  pure ⟨crossBlock, emit? state ⟨preheader.origin, headerCut⟩⟩

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.HeaderSplice
