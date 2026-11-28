module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.MLIR.CF.Defs

/-! # Typed CF with a smaller merge and a checked latch interface -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF

open SeaOfNodes.Diamond (Dataflow Val ValueSort dataPorts sortValue)
open SeaOfNodes.Loop.MLIR.CF (Op TargetOp model opcode)
open SeaOfNodes.MLIR (Word)
open SeaOfNodes.MLIR.Lowering (Scope encodeValues lowerCode operands valueWidth)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg Edge Frame)
open Diamond.MLIR.CF (Widths JumpTo blockNames entryNames lowerBlockWith returnFrame)
open Diamond.MLIR.CF.Pruned (lowerProjectedBlockWith)
open Diamond.Prune (HeaderProjection)
open RVSDG (Tuple Wires extend)
open Blocks (Bank)
open Blocks.Prune (Mask)

/-- Extend the existing labels with the original latch's narrower entry.
The routing map always uses this entry when the source targets the latch. -/
inductive Label {size : Nat} (header join latch : Fin size) {regs : List (ValueSort Width)}
    (carry merge atLatch : Mask regs) (out : ValueSort Width) : List Width → Type where
  | base {args : List Width} (label : MergePrune.MLIR.CF.Labels header join carry merge out args) :
      Label header join latch carry merge atLatch out args
  | latch : Label header join latch carry merge atLatch out (Widths atLatch.kept)

variable {regs : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size} {carry merge atLatch : Mask regs}
variable (p : Program src entry)

abbrev Target :=
  Cfg TargetOp (Label p.header p.join p.latch carry merge atLatch out) (Widths regs) [valueWidth out]

def liftEdge {Γ : List Width}
    (edge : Edge (MergePrune.MLIR.CF.Labels p.header p.join carry merge out) Γ) :
    Edge (Label p.header p.join p.latch carry merge atLatch out) Γ :=
  ⟨.base edge.label, edge.args⟩

def liftFrame (frame : Frame (MergePrune.MLIR.CF.Labels p.header p.join carry merge out)) :
    Frame (Label p.header p.join p.latch carry merge atLatch out) :=
  ⟨.base frame.label, frame.args⟩

/-- Each predecessor derives its operands from its post-block version map. -/
def jump : JumpTo regs size (Label p.header p.join p.latch carry merge atLatch out) :=
  fun scope versions id =>
    if id = p.latch then ⟨.latch, operands scope (atLatch.project versions)⟩
    else liftEdge p (MergePrune.MLIR.CF.jump p.header p.join carry merge scope versions id)

def latchFrame (bank : Bank (regs := atLatch.kept) model) :
    Frame (Label p.header p.join p.latch carry merge atLatch out) :=
  ⟨.latch, encodeValues bank⟩

def siteFrame (id : Fin size) (bank : Bank (regs := regs) model) :
    Frame (Label p.header p.join p.latch carry merge atLatch out) :=
  if id = p.latch then latchFrame p (atLatch.project bank)
  else liftFrame p (MergePrune.MLIR.CF.siteFrame p.header p.join carry merge id bank)

def headerFrame (bank : Bank (regs := carry.kept) model) :
    Frame (Label p.header p.join p.latch carry merge atLatch out) :=
  ⟨.base .header, encodeValues bank⟩

def mergeFrame (bank : Bank (regs := merge.kept) model) :
    Frame (Label p.header p.join p.latch carry merge atLatch out) :=
  ⟨.base .merge, encodeValues bank⟩

def exitFrame (value : sortValue Word out) : Frame (Label p.header p.join p.latch carry merge atLatch out) :=
  returnFrame (.base .exit) value

/-- State before the final predecessor executes. For a direct edge this
is the input to the split; otherwise it is before the last arm block. -/
def segmentPredecessorBank {target : Fin size} :
    {site : Fin size} → Chain.Segment src target site →
      Bank (regs := regs) model → Bank (regs := regs) model → Bank (regs := regs) model
  | _, .empty, beforeSplit, _ => beforeSplit
  | _, .jump site _ rest, _, current =>
    segmentPredecessorBank rest current ((src site).body.eval model current)

/-- Recover the local input of the original merge predecessor for this route. -/
def predecessorBank (old : Bank (regs := regs) model) (occurrence : Occurrence) : Bank (regs := regs) model :=
  let outer := (src p.header).body.eval model old
  match occurrence with
  | .innerTrue | .innerFalse =>
    segmentPredecessorBank (p.arm occurrence) outer ((src p.inner).body.eval model outer)
  | .outerFalse => segmentPredecessorBank (p.arm occurrence) old outer

def latchTerminator {args : List (SeaOfNodes.Diamond.Ty Width)} {past : List (List (SeaOfNodes.Diamond.Ty Width))} {Γ : List Width}
    (scope : Scope args past Γ) (packet : Wires args past (packetPorts out carry)) :
    Silmaril.MLIR.CF.Terminator (Label p.header p.join p.latch carry merge atLatch out) [valueWidth out] Γ :=
  match packet with
  | .cons test (.cons returned feedback) =>
    .condBr (scope.resolveValue test) ⟨.base .header, operands scope feedback⟩
      ⟨.base .exit, .cons (scope.resolveValue returned) .nil⟩

/-- The observed guard chooses between two already resolved packets. -/
def packetFrame (packet : Tuple (Val Word) (packetPorts out carry)) :
    Frame (Label p.header p.join p.latch carry merge atLatch out) :=
  match packet with
  | .cons test (.cons returned feedback) =>
    if test.down then headerFrame p feedback else exitFrame p returned

abbrev LatchBlock :=
  Silmaril.MLIR.CF.Block TargetOp (Label p.header p.join p.latch carry merge atLatch out)
    (Widths atLatch.kept ++ Widths regs) [valueWidth out]

/-- The latch terminator accepts any scoped table with the checked packet
interface, including a table with fewer pure producers. -/
def latchCode {sigs : List (List (SeaOfNodes.Diamond.Ty Width))}
    (flow : Dataflow Op (dataPorts atLatch.kept) [] sigs)
    (packet : Wires (dataPorts atLatch.kept) (extend [] sigs) (packetPorts out carry)) :
    LatchBlock (carry := carry) (merge := merge) (atLatch := atLatch) p :=
  lowerCode opcode flow ⟨blockNames (Widths regs) atLatch.kept, PUnit.unit⟩
    fun scope => latchTerminator p scope packet

/-- Replace the tested latch's code at the same typed label. -/
def withLatch (cfg : Target (carry := carry) (merge := merge) (atLatch := atLatch) p)
    (block : LatchBlock (carry := carry) (merge := merge) (atLatch := atLatch) p) :
    Target (carry := carry) (merge := merge) (atLatch := atLatch) p where
  entry := cfg.entry
  block
    | .latch => block
    | .base label => cfg.block (.base label)

/-- Emit two original blocks. The common merge branches with the latch's
typed inputs, and the latch resolves both outgoing packets in its own scope. -/
def lower (projected : HeaderProjection (src p.header).body carry)
    (checked : Split.Checked p carry merge atLatch) : Target (carry := carry) (merge := merge) (atLatch := atLatch) p where
  entry := lowerBlockWith (jump p) (.base .exit) (src entry) ⟨entryNames regs, PUnit.unit⟩
  block
    | .base .header => lowerProjectedBlockWith (jump p) (.base .exit) (src p.header) projected (Widths regs)
    | .base .merge =>
      lowerCode opcode checked.mergeTransfer.flow ⟨blockNames (Widths regs) merge.kept, PUnit.unit⟩
        fun scope => .br ⟨.latch, operands scope checked.mergeTransfer.outgoing⟩
    | .base (.site id _ _) => lowerBlockWith (jump p) (.base .exit) (src id)
        ⟨blockNames (Widths regs) regs, PUnit.unit⟩
    | .base .exit => .terminator (.ret (.cons .here .nil))
    | .latch => latchCode p checked.latchTransfer.flow checked.latchTransfer.outgoing

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF
