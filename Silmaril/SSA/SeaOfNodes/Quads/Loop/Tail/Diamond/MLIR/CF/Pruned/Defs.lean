module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Defs

/-! # Emit the checked smaller carried bank as CF header arguments -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model opcode)
open SeaOfNodes.MLIR.Lowering (encodeValues lowerCode operands valueWidth)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

inductive Label {size : Nat} (header : Fin size) (regs kept : List (ValueSort Width))
    (out : ValueSort Width) : List Width → Type where
  | header : Label header regs kept out (Widths kept)
  | site (id : Fin size) (different : id ≠ header) : Label header regs kept out (Widths regs)
  | exit : Label header regs kept out [valueWidth out]

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {p : Program src entry} {mask : Mask regs}

abbrev Target (header : Fin size) (mask : Mask regs) (out : ValueSort Width) :=
  Cfg TargetOp (Label header regs mask.kept out) (Widths regs) [valueWidth out]

/-- Only edges targeting the original header project their argument bank. -/
def jump (header : Fin size) (mask : Mask regs) : JumpTo regs size (Label header regs mask.kept out) :=
  fun scope versions id =>
    if different : id ≠ header then ⟨.site id different, operands scope versions⟩
    else ⟨.header, operands scope (mask.project versions)⟩

def headerFrame (header : Fin size) (mask : Mask regs) (bank : Bank (regs := regs) model) :
    Frame (Label header regs mask.kept out) :=
  ⟨.header, encodeValues (mask.project bank)⟩

def siteFrame (header : Fin size) (mask : Mask regs) (id : Fin size) (bank : Bank (regs := regs) model) :
    Frame (Label header regs mask.kept out) :=
  if different : id ≠ header then ⟨.site id different, encodeValues bank⟩
  else headerFrame header mask bank

def exitFrame (header : Fin size) (mask : Mask regs)
    (value : SeaOfNodes.Diamond.sortValue SeaOfNodes.MLIR.Word out) :
    Frame (Label header regs mask.kept out) :=
  returnFrame .exit value

/-- Only the header uses the checked renamed producer table. The entry,
arms, merge and latch use the full-bank block compiler. -/
def lower (checked : Checked p mask) : Target p.header mask out where
  entry := lowerBlockWith (jump p.header mask) .exit (src entry) ⟨entryNames regs, PUnit.unit⟩
  block
    | .header =>
      lowerCode opcode checked.flow ⟨blockNames (Widths regs) mask.kept, PUnit.unit⟩
        fun scope => lowerTerminatorWith (jump p.header mask) .exit scope checked.outgoing (src p.header).terminator
    | .site id _ => lowerBlockWith (jump p.header mask) .exit (src id) ⟨blockNames (Widths regs) regs, PUnit.unit⟩
    | .exit => .terminator (.ret (.cons .here .nil))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned
