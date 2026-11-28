module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Example.Defs

/-! # Execute a latch with one fewer pure producer -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Example

open Diamond.MLIR.CF.Example
  (add constant count decrement input num positive regs result stride)
open Diamond.Prune (HeaderProjection)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Nested.Numbered (KeptResult checkResult)
open Silmaril.MLIR.CF (Frame)
open Silmaril.MLIR.Pure (OpSignature)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)

/-- The first comparison is overwritten before any read. The constant
254 survives only through a chain of operands, where it becomes 255
before decrementing the counter. -/
def source : Source Op regs num 7 := fun id =>
  let block := Latch.Example.source id
  if id = 6 then
    {block with body := [positive count, constant decrement 254, add decrement decrement stride,
      add count count decrement, positive count]}
  else block

def plan : Program source 0 := (Nested.check source 0).get (by rfl)

abbrev carry := Nested.MLIR.CF.carriedMask plan
abbrev mask := Latch.mergeMask plan carry
abbrev atLatch := Split.latchMask plan carry

def projected : HeaderProjection (source plan.header).body carry := (Nested.MLIR.CF.prune plan).get (by rfl)
def checked : Latch.Checked plan carry mask := (Latch.prune plan carry).get (by rfl)
def cut : Split.Checked plan carry mask atLatch := (Split.prepare plan checked).get (by rfl)

def shortened : Split.DeadProducer.Checked cut.latchTransfer :=
  (Split.DeadProducer.first cut.latchTransfer).get (by rfl)

def keptResult : KeptResult plan (mask := carry) := (checkResult plan carry).get (by rfl)

/-- In order: a transitive operand, the counter and the final predicate. -/
def refuses : Bool × Bool × Bool :=
  ((Split.DeadProducer.check cut.latchTransfer (.later .here)).isNone,
    (Split.DeadProducer.check cut.latchTransfer (.later (.later (.later .here)))).isNone,
    (Split.DeadProducer.check cut.latchTransfer (.later (.later (.later (.later .here))))).isNone)

def bindingCount {O : OpSignature} {T : List Width → Type} :
    {Γ : List Width} → Silmaril.MLIR.Pure.Code O T Γ → Nat
  | _, .terminator _ => 0
  | _, .letOp _ _ rest => 1 + bindingCount rest

/-- Count actual operations in the two emitted CF latch blocks. -/
def latchCounts : Nat × Nat :=
  (bindingCount ((CF.lower plan projected cut).block .latch),
    bindingCount ((DeadProducer.lower plan projected cut shortened).block .latch))

def runSource (fuel : Nat) : Option Nat :=
  (source.runFrom model fuel 0 input).map BitVec.toNat

def runCF (fuel : Nat) : Option Nat :=
  ((DeadProducer.lower plan projected cut shortened).run evalOp fuel (encodeValues input)).map
    (fun env => (env.get .here).toNat)

def runRVSDG (fuel : Nat) : Option Nat :=
  ((Latch.Numbered.lower plan projected checked keptResult).run (Join.model model) fuel input).map
    (fun values => (values.get .head).toNat)

def runSite (frame : Frame (Label plan.header plan.join plan.latch carry mask atLatch num)) :=
  ((DeadProducer.lower plan projected cut shortened).block frame.label).eval evalOp (fun term env => term.eval env)
    (frame.args.append (encodeValues input))

def runPredecessor (old : Bank (regs := regs) model) :=
  let occurrence := plan.selected model old
  runSite (siteFrame plan (plan.predecessor occurrence) (predecessorBank plan old occurrence))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Example
