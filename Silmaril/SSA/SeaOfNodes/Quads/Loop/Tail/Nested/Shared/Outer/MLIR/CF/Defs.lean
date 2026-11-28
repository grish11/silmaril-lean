module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Defs

/-! # Typed full-bank CF for the original outer-reconvergence table -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues valueWidth)
open Silmaril.MLIR.Arith (Width Env)
open Silmaril.MLIR.CF (Frame)
open Diamond.MLIR.CF (Label)
open Blocks (Bank)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)

/-- Emit the original table with one label per source block and full typed
edge operands in register order. -/
def lower (_plan : Program src entry) : Diamond.MLIR.CF.Target regs out size :=
  Diamond.MLIR.CF.lowerSource src entry

/-- Execute the emitted block at the original selected predecessor. -/
def outerArrival (input old : Bank (regs := regs) model) :
    Frame (Label regs out size) ⊕ Env [valueWidth out] :=
  let occurrence := p.toControl.selected model old
  let pred := (p.outerEdgeOccurrence (occurrence != .outerFalse)).1
  let before := p.outerPredecessorBank model old occurrence
  ((lower p).block (.site pred)).eval evalOp (fun term env => term.eval env)
    ((encodeValues before).append (encodeValues input))

/-- Execute the original tested latch with the bank after the selected
outer route, common tail, and final merge. -/
def latchSuccessor (input old : Bank (regs := regs) model) :
    Frame (Label regs out size) ⊕ Env [valueWidth out] :=
  let occurrence := p.toControl.selected model old
  let before := (src p.join).body.eval model (p.mergeBank model old occurrence)
  ((lower p).block (.site p.latch)).eval evalOp (fun term env => term.eval env)
    ((encodeValues before).append (encodeValues input))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF
