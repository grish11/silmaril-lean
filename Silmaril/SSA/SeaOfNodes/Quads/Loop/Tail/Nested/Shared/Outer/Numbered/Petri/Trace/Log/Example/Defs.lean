module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example.Defs

/-! The shared-tail 152 fixture, supplied as a flat list of real markings. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Example

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example (plan source)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example (input num regs result)
open RVSDG.NestedTheta.Petri (pending)
open RVSDG.NestedTheta.Petri.Replay (successors markingDecEq)

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)

section
variable {bank : List (ValueSort Width)} {sort : ValueSort Width} {size : Nat}
variable {src : Source Op bank sort size} {entry : Fin size}
variable (program : Program src entry) (initial : Bank (regs := bank) model)

/-- Take one certified firing at a time. During an activation the second
schedule chooses the last available firing instead of the first. -/
def markings (lastReady : Bool) : Nat → RootMark program → List (RootMark program)
  | 0, _ => []
  | fuel + 1, mark =>
    let moves := successors semantics (emitted program) initial PUnit.unit mark
    let choice := match ((entryCut program).rest semantics mark).1 with
      | .waiting _ _ => if lastReady then moves.getLast? else moves.head?
      | _ => moves.head?
    match choice with
    | none => []
    | some step => step.val :: markings lastReady fuel step.val

def different (left right : List (RootMark program)) : Bool :=
  letI := markingDecEq semantics colourEq (emitted program)
  decide (left ≠ right)

end

def flat (lastReady : Bool) : List (RootMark plan) :=
  markings plan input lastReady 200 (pending semantics (emitted plan))

def summarize {bank : List (ValueSort Width)} {sort : ValueSort Width} {size : Nat}
    {src : Source Op bank sort size} {entry : Fin size} (program : Program src entry)
    (initial : Bank (regs := bank) model) (showSlot : Bank (regs := bank) model → Nat)
    (showResult : Output sort → Nat) (roots : List (RootMark program)) :
    Option (List ((Nat × Nat) × Nat × Bool × Nat) × Nat) := do
  let found ← scan program initial roots
  let observations := (found.observations program initial).map fun seen =>
    ((seen.occurrence.1.val, seen.occurrence.2.val), showSlot seen.outer,
      seen.restarts, showSlot seen.next)
  some (observations, showResult (found.result program initial))

def showSlot (bank : Bank (regs := regs) model) : Nat := (bank.get result).toNat

def showResult (packet : Output num) : Nat := (packet.get .head).toNat

set_option maxHeartbeats 1000000 in
def summary : List (RootMark plan) → Option (List ((Nat × Nat) × Nat × Bool × Nat) × Nat) :=
  @summarize regs num 12 source 0 plan input showSlot showResult

def schedulesDiffer : Bool := different plan (flat false) (flat true)

def truncated : Bool := (scan plan input (flat false).dropLast).isNone

def malformed : Bool :=
  (scan plan input (pending semantics (emitted plan) :: flat false)).isNone

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Example
