module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Defs

/-! # Materialize a typed cut between the merge and the tested latch -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split

open SeaOfNodes.Diamond (Dataflow Model Ty Val ValueSort dataPorts)
open RVSDG (Tuple Wires extend)
open Join (Block)
open Diamond.Prune (headerTransferFor)
open Blocks (Bank)
open Blocks.Prune (Mask readSchedule renameFlow renameWires)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}

/-- Keep every producer in one source block and verify just the boundary
wires that the successor consumes. -/
structure Transfer (body : Block Op regs) (mask : Mask regs) {outputs : List (Ty Data)}
    (wires : Wires (dataPorts regs) (extend [] body.producers) outputs) where
  flow : Dataflow Op (dataPorts mask.kept) [] body.producers
  outgoing : Wires (dataPorts mask.kept) (extend [] body.producers) outputs
  flow_eq : renameFlow mask.rename (headerTransferFor body).flow = some flow
  outgoing_eq : renameWires mask.rename wires = some outgoing

def checkTransfer (body : Block Op regs) (mask : Mask regs) {outputs : List (Ty Data)}
    (wires : Wires (dataPorts regs) (extend [] body.producers) outputs) : Option (Transfer body mask wires) :=
  match flow_eq : renameFlow mask.rename (headerTransferFor body).flow,
        outgoing_eq : renameWires mask.rename wires with
  | some flow, some outgoing => some ⟨flow, outgoing, flow_eq, outgoing_eq⟩
  | _, _ => none

def Transfer.eval {body : Block Op regs} {mask : Mask regs} {outputs : List (Ty Data)}
    {wires : Wires (dataPorts regs) (extend [] body.producers) outputs}
    (transfer : Transfer body mask wires) (m : Model.{u, v, w} Op) (input : Bank (regs := mask.kept) m) :
    Tuple (Val m.value) outputs :=
  transfer.outgoing.read input (transfer.flow.eval m input PUnit.unit)

variable (p : Program src entry)

def latchWires (carry : Mask regs) :
    Wires (dataPorts regs) (extend [] (src p.latch).body.producers) (packetPorts out carry) :=
  observe p carry (headerTransferFor (src p.latch).body).outgoing

/-- Use the latch's own numbered scope. A slot read only after reassignment
is rooted at the new producer rather than at a block argument. -/
def latchMask (carry : Mask regs) : Mask regs :=
  let reads := readSchedule (headerTransferFor (src p.latch).body).flow ++ [(latchWires p carry).addresses]
  let live := RVSDG.NestedTheta.Liveness.sweep reads 0
  Mask.ofSlots (fun i => live.contains (.arg i)) regs

def mergeWires (latch : Mask regs) :
    Wires (dataPorts regs) (extend [] (src p.join).body.producers) (dataPorts latch.kept) :=
  latch.project (headerTransferFor (src p.join).body).outgoing

/-- Keep the shared merge–latch certificate and validate a cut at the
original edge with independently scoped producer tables. -/
structure Checked (p : Program src entry) (carry merge latch : Mask regs) where
  whole : Latch.Checked p carry merge
  mergeTransfer : Transfer (src p.join).body merge (mergeWires p latch)
  latchTransfer : Transfer (src p.latch).body latch (latchWires p carry)

def check {carry merge : Mask regs} (whole : Latch.Checked p carry merge) (latch : Mask regs) :
    Option (Checked p carry merge latch) := do
  let mergeTransfer ← checkTransfer (src p.join).body merge (mergeWires p latch)
  let latchTransfer ← checkTransfer (src p.latch).body latch (latchWires p carry)
  return ⟨whole, mergeTransfer, latchTransfer⟩

def prepare {carry merge : Mask regs} (whole : Latch.Checked p carry merge) :
    Option (Checked p carry merge (latchMask p carry)) :=
  check p whole (latchMask p carry)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split
