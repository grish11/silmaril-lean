module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Example.Defs

/-! # Compile the existing dead-chain fixture from its ordered source table -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Example

open Diamond.MLIR.CF.Example (input num regs result stride test)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open SeaOfNodes.Pure.Deletion (delete?)
open Nested.Numbered (nextBank)

abbrev source := Iteration.Example.source

/-- The inner false edge bypasses the common merge and is refused by the recognizer. -/
def skipsMerge : Source Op regs num 7 := fun id =>
  if id = 2 then {source id with terminator := .branch test (.jump 3) (.jump 6)}
  else source id

/-- The recognized header now leaves the complete typed bank live. -/
def fullHeader : Source Op regs num 7 := fun id =>
  if id = 1 then {source id with body := []}
  else source id

/-- Both inner slots now go straight from block 2 to merge 4.
The outer false arm still contributes a distinct bank via block 3. -/
def parallelInner : Source Op regs num 6 := fun id =>
  if id = 0 then ⟨(source 0).body, .transfer (.jump 1)⟩
  else if id = 1 then ⟨(source 1).body, .branch test (.jump 2) (.jump 3)⟩
  else if id = 2 then ⟨(source 2).body, .branch test (.jump 4) (.jump 4)⟩
  else if id = 3 then ⟨(source 4).body, .transfer (.jump 4)⟩
  else if id = 4 then ⟨(source 5).body, .transfer (.jump 5)⟩
  else ⟨(source 6).body, .branch test (.jump 1) (.ret result)⟩

/-- A common nonempty arm before the merge still violates disjointness. -/
def sharedInnerArm : Source Op regs num 7 := fun id =>
  if id = 2 then {source id with terminator := .branch test (.jump 3) (.jump 3)}
  else source id

def runAt {size : Nat} {table : Source Op regs num size} {entry : Fin size}
    (targets : Targets table entry) (sourceFuel cfFuel activations : Nat) :
    Option Nat × Option Nat × Option Nat :=
  ((table.runFrom model sourceFuel entry input).map BitVec.toNat,
    (targets.cf.run evalOp cfFuel (encodeValues input)).map (fun result => (result.get .here).toNat),
    (targets.numbered.run (Join.model model) activations input).map (fun result => (result.get .head).toNat))

def parallelTrace (targets : Targets parallelInner 0) : List ((Nat × Nat) × Option (Bool × Nat)) :=
  let p := targets.program
  let first := (parallelInner 0).body.eval model input
  let second := nextBank p model first
  let third := nextBank p model second
  [first, second, third].map fun old =>
    let edge := p.incomingEdge (p.selected model old)
    let packet := (targets.packetRegion.run (Join.model model) 0 ((carry p).project old)).map fun
      | .cons guard (.cons word _) => (guard.down, word.toNat)
    ((edge.1.val, edge.2.val), packet)

/-- Find the last emitted latch producer, check that the full packet
protects it, and locate its only use in the carried stride field. -/
def strideUse (targets : Targets source 0) : Option (Nat × Bool) := do
  let port ← (carry targets.program).rename stride
  let table := targets.prepared.final
  let candidate ← (SeaOfNodes.GVN.Pass.candidates table.flow).getLast?
  let address := candidate.2.origin.address
  let feedback := table.packet.get (.tail (.tail port))
  return (port.index, (delete? candidate.2 table.packet).isNone && feedback.address == address &&
    table.packet.addresses.count address == 1)

def latchOps (targets : Targets source 0) : Nat × Nat :=
  let p := targets.program
  let skip := (source p.header).body.producers.length + (source p.join).body.producers.length
  let tests := Numbered.DeadProducer.Example.latchTests.thetaTests targets.numbered ⟨4, by change 4 < 5; decide⟩
  (MLIR.CF.DeadProducer.Example.bindingCount (targets.cf.block .latch), (tests.drop skip).length)

structure Report where
  cuts : List Nat
  latchOps : Nat × Nat
  strideUse : Option (Nat × Bool)
  predecessors : List Nat
  guardAndExit : List (Option (Bool × Nat))
  returned : Option Nat × Option Nat × Option Nat
  belowReturn : Option Nat × Option Nat × Option Nat
  deriving Repr

def report (targets : Targets source 0) : Report :=
  let p := targets.program
  let first := (source 0).body.eval model input
  let second := nextBank p model first
  let third := nextBank p model second
  let states := [first, second, third]
  let predecessors := states.map (fun old => (p.predecessor (p.selected model old)).val)
  let guardAndExit := states.map fun old =>
    (targets.packetRegion.run (Join.model model) 0 ((carry p).project old)).map fun
      | .cons guard (.cons word _) => (guard.down, word.toNat)
  ⟨targets.prepared.positions, latchOps targets, strideUse targets, predecessors, guardAndExit,
    runAt targets 14 15 3, runAt targets 13 14 2⟩

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Example
