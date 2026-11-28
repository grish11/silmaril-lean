module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Normalize.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Example.Defs

/-! Delay one overwritten quad in the actual numbered preheader. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Normalize.Example

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (finished pending)
open RVSDG.NestedTheta.Petri.Replay (successors markingDecEq)

section
variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry) (initial : Bank (regs := regs) model)

def schedule : Nat → (start : RootMark p) →
    {marks : List (RootMark p) // List.IsChain (RootFire p initial) (start :: marks)}
  | 0, start => ⟨[], .singleton start⟩
  | fuel + 1, start =>
    let moves := successors semantics (emitted p) initial PUnit.unit start
    match (if thetaPending p start then moves.getLast? else moves.head?) with
    | none => ⟨[], .singleton start⟩
    | some move =>
      let later := schedule fuel move.val
      ⟨move.val :: later.val, .cons_cons move.property later.property⟩

def firstEntry (roots : List (RootMark p)) : Option (RootMark p) :=
  roots.find? fun root => !thetaPending p root

def sameTheta (left right : List (RootMark p)) : Bool :=
  letI := markingDecEq semantics colourEq (entryTail p)
  decide (thetaChanges p left = thetaChanges p right)

end

open Diamond.MLIR.CF.Example (constant selector input num regs)
open Outer.Numbered.Example (source)
open Log.Example (showResult showSlot)

def sourceWithOverwrite : Source Op regs num 12 := fun id =>
  if id = 0 then {source id with body := constant selector 42 :: (source id).body}
  else source id

def plan : Program sourceWithOverwrite 0 := (Outer.check sourceWithOverwrite 0).get (by rfl)

def flat : List (RootMark plan) :=
  (schedule plan input 200 (pending semantics (emitted plan))).val

def preheaderReadyAtEntry : Option Bool := (firstEntry plan flat).map fun mark =>
  (finished semantics (preheader plan) input PUnit.unit ((entryCut plan).observe semantics mark)).isSome

def outputWord : Option Nat :=
  (finished semantics (emitted plan) input PUnit.unit
    (flat.getLastD (pending semantics (emitted plan)))).map showResult

def summary : Option (List ((Nat × Nat) × Nat × Bool × Nat) × Nat) := do
  let found ← scanNormalized plan input flat
  let observations := (found.observations plan input).map fun seen =>
    ((seen.occurrence.1.val, seen.occurrence.2.val), showSlot seen.outer,
      seen.restarts, showSlot seen.next)
  return (observations, showResult (found.result plan input))

def report :=
  (preheaderReadyAtEntry, outputWord, (scan plan input flat).isSome, summary,
    sameTheta plan flat (normalize plan flat), (scanNormalized plan input flat.dropLast).isNone,
    (scanNormalized plan input (pending semantics (emitted plan) :: flat)).isNone)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Normalize.Example
