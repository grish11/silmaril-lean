module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Completeness.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Example.Defs

/-! Change scheduling inside the actual outer-true child, which contains
the inner split and shared inner suffix. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Completeness.Example

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (Marking pending)
open RVSDG.NestedTheta.Petri.Replay (successors markingDecEq)

section

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

abbrev InnerMark := Marking semantics (Prefix.outerArm p.toRoutes 0)

def innerMark (root : RootMark p) : Option (InnerMark p) :=
  match ((entryCut p).rest semantics root).1 with
  | .waiting _ (_, body) =>
    match ((headerCut p).rest semantics body).2.1 with
    | .waiting arm (_, child) =>
      let i : Fin 2 := arm
      if same : i = 0 then
        some (cast (congrArg (fun i => Marking semantics (Prefix.outerArm p.toRoutes i)) same) child)
      else none
    | _ => none
  | _ => none

/-- Prefer the last child-local move when the selected inner region
offers several legal firings. Other phases retain the original choice. -/
def childLast : Nat → RootMark p → List (RootMark p)
  | 0, _ => []
  | fuel + 1, root =>
    let moves := successors semantics (emitted p) input PUnit.unit root
    let childMoves : List {after : RootMark p // RootFire p input root after} := match innerMark p root with
      | none => []
      | some before =>
        letI := markingDecEq semantics colourEq (Prefix.outerArm p.toRoutes 0)
        moves.filter fun move => match innerMark p move.val with
          | none => false
          | some after => decide (before ≠ after)
    match childMoves.getLast?.or moves.head? with
    | none => []
    | some move => move.val :: childLast fuel move.val

/-- Ignore repeated child markings while an unrelated root firing occurs.
A difference in these histories is a change inside the live child. -/
def innerHistory (roots : List (RootMark p)) : List (InnerMark p) :=
  letI := markingDecEq semantics colourEq (Prefix.outerArm p.toRoutes 0)
  (roots.filterMap (innerMark p)).eraseRepsBy fun left right => decide (left = right)

def distinctInner (left right : List (RootMark p)) : Bool :=
  letI := markingDecEq semantics colourEq (Prefix.outerArm p.toRoutes 0)
  decide (innerHistory p left ≠ innerHistory p right)

end

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example (plan)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example (input)
open Log.Example (flat summary)

def alternate : List (RootMark plan) :=
  childLast plan input 200 (pending semantics (emitted plan))

def report := (summary (flat false), summary alternate, distinctInner plan (flat false) alternate)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log.Completeness.Example
