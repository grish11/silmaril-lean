module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Defs

/-! # Checked projection at the common quad merge -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune

open SeaOfNodes.Diamond (Model ValueSort)
open Diamond.Prune (HeaderProjection boundaryMaskFor checkHeader)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}

abbrev Checked (p : Program src entry) (mask : Mask regs) :=
  HeaderProjection (src p.join).body mask

/-- Every merge producer must resolve its operands, and the complete
post-merge bank must be reconstructible before entering the latch. -/
def checkMask (p : Program src entry) (mask : Mask regs) : Option (Checked p mask) :=
  checkHeader (src p.join).body mask

def mergeMask (p : Program src entry) : Mask regs :=
  boundaryMaskFor (src p.join).body (fun _ => false)

def prune (p : Program src entry) : Option (Checked p (mergeMask p)) :=
  checkMask p (mergeMask p)

/-- All occurrences use the same ordered projection, on their own
independently compiled reaching versions. -/
def incoming (p : Program src entry) (mask : Mask regs) (m : Model.{u, v, w} Op)
    (old : Bank (regs := regs) m) (occurrence : Occurrence) : Bank (regs := mask.kept) m :=
  mask.project (p.mergeBank m old occurrence)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune
