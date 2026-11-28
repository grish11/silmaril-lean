module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Example.Defs

/-! # Two cuts, three predecessor occurrences and a feedback-only producer -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Example

open Diamond.MLIR.CF.Example (add constant count decrement input num positive regs stride zero)
open Diamond.Prune (HeaderProjection)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open SeaOfNodes.Pure.Deletion (delete?)
open SeaOfNodes.Pure.Deletion.Iteration (first?)
open SeaOfNodes.GVN (Producer)
open Nested.Numbered (KeptResult checkResult nextBank)
open Blocks (Bank)

/-- The first constant has a use until the comparison is removed. The last
stride update supplies a later feedback field, after the guard and exit. -/
def source : Source Op regs num 7 := fun id =>
  let block := Latch.Example.source id
  if id = 6 then
    {block with body := [constant decrement 200, positive decrement, constant decrement 254,
      add decrement decrement stride, add count count decrement, positive count, add stride stride zero]}
  else block

def plan : Program source 0 := (Nested.check source 0).get (by rfl)

abbrev carry := Nested.MLIR.CF.carriedMask plan
abbrev merge := Latch.mergeMask plan carry
abbrev atLatch := Split.latchMask plan carry

def projected : HeaderProjection (source plan.header).body carry := (Nested.MLIR.CF.prune plan).get (by rfl)
def whole : Latch.Checked plan carry merge := (Latch.prune plan carry).get (by rfl)
def checked : Split.Checked plan carry merge atLatch := (Split.prepare plan whole).get (by rfl)
def keptResult : KeptResult plan (mask := carry) := (checkResult plan carry).get (by rfl)

def prepared : Prepared checked := prepare checked

def initial := Split.DeadProducer.originalTable checked.latchTransfer

def refusesBeforeRescan : Bool :=
  let constantUse : Producer initial.flow num := .here
  (delete? constantUse initial.packet).isNone

def feedbackOnly : Producer prepared.final.flow num := .later (.later (.later (.later .here)))

/-- Checking just guard and exit would accept the bad cut. Checking the
complete packet refuses it, and its one use is at carried slot three. -/
def feedbackCheck : Bool × Bool × Nat × Bool :=
  let table := prepared.final
  let guardExit := RVSDG.Tuple.cons (table.packet.get .head)
    (.cons (table.packet.get (.tail .head)) .nil)
  let stridePort := (carry.rename stride).get (by rfl)
  let use := table.packet.get (.tail (.tail stridePort))
  let address := feedbackOnly.origin.address
  ((delete? feedbackOnly guardExit).isSome, (delete? feedbackOnly table.packet).isNone,
    stridePort.index, use.address == address && table.packet.addresses.count address == 1)

def settled : Bool := (first? prepared.final).isNone

def cf := lowerCF plan projected checked prepared
def numbered := lowerNumbered plan projected checked prepared keptResult

def latchCounts : (Nat × Nat) × (Nat × Nat) :=
  let bindingCount := @MLIR.CF.DeadProducer.Example.bindingCount
  let oldCF := MLIR.CF.lower plan projected checked
  let oldNumbered := Numbered.lower plan projected whole keptResult
  let tests := @Numbered.DeadProducer.Example.latchTests.thetaTests
  let skip := (source plan.header).body.producers.length + (source plan.join).body.producers.length
  ((bindingCount (oldCF.block .latch), bindingCount (cf.block .latch)),
    (((tests oldNumbered ⟨4, by decide⟩).drop skip).length, ((tests numbered ⟨4, by decide⟩).drop skip).length))

def first : Bank (regs := regs) model := (source 0).body.eval model input
def second : Bank (regs := regs) model := nextBank plan model first
def third : Bank (regs := regs) model := nextBank plan model second

def predecessorOrder : List Nat :=
  [first, second, third].map (fun old => (plan.predecessor (plan.selected model old)).val)

def runBody (old : Bank (regs := regs) model) :=
  (Numbered.DeadProducer.thetaWith plan projected checked prepared.final).run (Join.model model) 0
    (carry.project old)

def feedback : List (Option (Nat × Nat × Nat)) :=
  let port := (carry.rename count).get (by rfl)
  [first, second, third].map fun old => (runBody old).map fun
    | .cons tag packet => (tag.down.val, (packet.get port).toNat, (packet.get keptResult.val).toNat)

def runSource (fuel : Nat) : Option Nat :=
  (source.runFrom model fuel 0 input).map BitVec.toNat

def runCF (fuel : Nat) : Option Nat :=
  (cf.run evalOp fuel (encodeValues input)).map (fun env => (env.get .here).toNat)

def runNumbered (fuel : Nat) : Option Nat :=
  (numbered.run (Join.model model) fuel input).map (fun values => (values.get .head).toNat)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Example
