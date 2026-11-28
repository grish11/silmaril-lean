module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Trace.Log.Defs

/-! A complete log in the fully marked entry profile, stated without
running the scanner or supplying activation boundaries. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)
open RVSDG.NestedTheta.Petri (finished pending)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} (p : Program src entry)
variable (input : Bank (regs := regs) model)

def thetaPending (mark : RootMark p) : Bool :=
  match ((entryCut p).rest semantics mark).1 with
  | .pending => true
  | _ => false

/-- At the step leaving the pending θ phase, all preheader vertices must
already have published. All other adjacent pairs just use original Fire. -/
def ProfileStep (before after : RootMark p) : Prop :=
  RootFire p input before after ∧
    (thetaPending p before = true → thetaPending p after = false →
      (finished semantics (preheader p) input PUnit.unit ((entryCut p).observe semantics after)).isSome)

/-- The listed markings are all post-firing. Completion is read at the
last supplied marking with the existing semantics. -/
def LegalComplete (roots : List (RootMark p)) : Prop :=
  List.IsChain (ProfileStep p input) (pending semantics (emitted p) :: roots) ∧
    (finished semantics (emitted p) input PUnit.unit (roots.getLastD (pending semantics (emitted p)))).isSome

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Log
