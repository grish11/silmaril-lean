module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Defs

/-! Read the existing outer γ and θ boundaries in a supplied marking. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (Marking finished pending)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)

def readOuter (old : Bank (regs := regs) model) (mark : Marking semantics (thetaBody p)) :
    Option (Bank (regs := regs) model) :=
  finished semantics (outerRegion p) old PUnit.unit ((outerCut p).2.2.observe semantics mark)

def afterLatch
    (preheader : Marking semantics (.ofBase (entryCode (src := src) (entry := entry))))
    (again : Bool) (bank : Bank (regs := regs) model) : Marking semantics (emitted p) :=
  if again then atBody p preheader bank (pending semantics (thetaBody p))
  else (entryCut p).attach semantics preheader (.done bank, PUnit.unit)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri
