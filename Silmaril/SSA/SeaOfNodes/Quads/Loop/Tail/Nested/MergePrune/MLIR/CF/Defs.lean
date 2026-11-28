module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Defs

/-! # Typed CF projects the header and common merge independently -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF

open SeaOfNodes.Diamond (ValueSort sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (encodeValues operands valueWidth)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Diamond.MLIR.CF (Widths JumpTo blockNames entryNames lowerBlockWith returnFrame)
open Diamond.MLIR.CF.Pruned (lowerProjectedBlockWith)
open Diamond.Prune (HeaderProjection)
open Blocks (Bank)
open Blocks.Prune (Mask)

inductive Label {size : Nat} (header join : Fin size)
    (regs headerRegs mergeRegs : List (ValueSort Width)) (out : ValueSort Width) : List Width → Type where
  | header : Label header join regs headerRegs mergeRegs out (Widths headerRegs)
  | merge : Label header join regs headerRegs mergeRegs out (Widths mergeRegs)
  | site (id : Fin size) (notHeader : id ≠ header) (notMerge : id ≠ join) :
      Label header join regs headerRegs mergeRegs out (Widths regs)
  | exit : Label header join regs headerRegs mergeRegs out [valueWidth out]

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}

abbrev Labels (header join : Fin size) (carry merge : Mask regs) (out : ValueSort Width) :=
  Label header join regs carry.kept merge.kept out

abbrev Target (header join : Fin size) (carry merge : Mask regs) (out : ValueSort Width) :=
  Cfg TargetOp (Labels header join carry merge out) (Widths regs) [valueWidth out]

/-- Every predecessor uses its own resolved versions. The target label
determines which interface to pass. -/
def jump (header join : Fin size) (carry merge : Mask regs) :
    JumpTo regs size (Labels header join carry merge out) :=
  fun scope versions id =>
    if atHeader : id = header then ⟨.header, operands scope (carry.project versions)⟩
    else if atMerge : id = join then ⟨.merge, operands scope (merge.project versions)⟩
    else ⟨.site id atHeader atMerge, operands scope versions⟩

def headerFrame (header join : Fin size) (carry merge : Mask regs) (bank : Bank (regs := regs) model) :
    Frame (Labels header join carry merge out) :=
  ⟨.header, encodeValues (carry.project bank)⟩

def mergeFrame (header join : Fin size) (carry merge : Mask regs)
    (bank : Bank (regs := merge.kept) model) : Frame (Labels header join carry merge out) :=
  ⟨.merge, encodeValues bank⟩

def siteFrame (header join : Fin size) (carry merge : Mask regs) (id : Fin size)
    (bank : Bank (regs := regs) model) : Frame (Labels header join carry merge out) :=
  if atHeader : id = header then headerFrame header join carry merge bank
  else if atMerge : id = join then mergeFrame header join carry merge (merge.project bank)
  else ⟨.site id atHeader atMerge, encodeValues bank⟩

variable {src : Source Op regs out size} {entry : Fin size} {carry merge : Mask regs}

/-- The original terminators and block identities are preserved. The
header and the common merge reconstruct their own checked outgoing banks. -/
def lower (p : Program src entry) (projected : HeaderProjection (src p.header).body carry)
    (checked : Checked p merge) : Target p.header p.join carry merge out where
  entry := lowerBlockWith (jump p.header p.join carry merge) .exit (src entry) ⟨entryNames regs, PUnit.unit⟩
  block
    | .header => lowerProjectedBlockWith (jump p.header p.join carry merge) .exit
        (src p.header) projected (Widths regs)
    | .merge => lowerProjectedBlockWith (jump p.header p.join carry merge) .exit
        (src p.join) checked (Widths regs)
    | .site id _ _ => lowerBlockWith (jump p.header p.join carry merge) .exit
        (src id) ⟨blockNames (Widths regs) regs, PUnit.unit⟩
    | .exit => .terminator (.ret (.cons .here .nil))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF
