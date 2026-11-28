module

public import Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.Defs

/-! Feedback driver for the emitted single-buffer MemRef activation. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef

open RVSDG (Tuple)
open Silmaril.MLIR.MemRef (Buffer)

variable {args : List ValueSort} {cells : Nat}

/-- Execute the emitted activation until it exits after exactly the given
number of backedges. Count zero still executes the first activation.
Each backedge passes the entire updated buffer to the same typed input. -/
def runAfter (graph : Graph args) (input : Tuple (Val cells) args) :
    Nat → Buffer cells → Option (Word × Buffer cells)
  | 0, initial => (observeActivation graph input initial).elim some (fun _ => none)
  | count + 1, initial =>
    (observeActivation graph input initial).elim (fun _ => none) (runAfter graph input count)

/-- The finite return of the emitted activation under feedback. This uses a
driver around the typed block, with the buffer as the recursive state. -/
noncomputable def observe (graph : Graph args) (input : Tuple (Val cells) args)
    (initial : Buffer cells) : Part (Word × Buffer cells) :=
  Silmaril.Elgot.Part.run (fun buffer => Part.some (observeActivation graph input buffer)) initial

end Silmaril.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef
