module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.Prune.Defs

/-! # Emit the checked smaller carried bank as CF header arguments -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model opcode)
open SeaOfNodes.MLIR.Lowering (Names encodeValues lowerCode operands valueWidth)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg Frame)
open RVSDG (Tuple)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked HeaderProjection)

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

/-- Emit a projected block using its checked flow and latest outgoing versions. -/
def lowerProjectedBlockWith {Labels : List Width → Type} (jumpTo : JumpTo regs size Labels)
    (exit : Labels [valueWidth out]) (block : SourceBlock Op regs out size)
    (projected : HeaderProjection block.body mask) (captures : List Width) :
    Silmaril.MLIR.CF.Block TargetOp Labels (Widths mask.kept ++ captures) [valueWidth out] :=
  lowerCode opcode projected.flow ⟨blockNames captures mask.kept, PUnit.unit⟩
    fun scope => lowerTerminatorWith jumpTo exit scope projected.outgoing block.terminator

/-- Emit the original source blocks with a certified projection at one
header. Every edge still uses the source terminator and its final versions. -/
def lowerSourceWith (src : Source Op regs out size) (entry header : Fin size)
    (projected : HeaderProjection (src header).body mask) {Γ : List Width}
    (names : Tuple (Names Γ) (dataPorts regs)) :
    Cfg TargetOp (Label header regs mask.kept out) Γ [valueWidth out] where
  entry := lowerBlockWith (jump header mask) .exit (src entry) ⟨names, PUnit.unit⟩
  block
    | .header => lowerProjectedBlockWith (jump header mask) .exit (src header) projected Γ
    | .site id _ => lowerBlockWith (jump header mask) .exit (src id) ⟨blockNames Γ regs, PUnit.unit⟩
    | .exit => .terminator (.ret (.cons .here .nil))

/-- Compile the preheader with the supplied external argument names.
Successor blocks still bind their original local and carried banks. -/
def lowerWith (checked : Checked p mask) {Γ : List Width}
    (names : Tuple (Names Γ) (dataPorts regs)) :
    Cfg TargetOp (Label p.header regs mask.kept out) Γ [valueWidth out] :=
  lowerSourceWith src entry p.header checked.toHeaderProjection names

/-- Bind the external inputs in register order. -/
def lower (checked : Checked p mask) : Target p.header mask out :=
  lowerWith checked (entryNames regs)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned
