module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Defs

/-! # Merge inputs needed by the tested latch and feedback -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch

open SeaOfNodes.Diamond (Dataflow Model Ty Val ValueSort dataPorts)
open RVSDG (Tuple Wires extend)
open Diamond.Prune (headerTransferFor)
open Blocks (Bank)
open Blocks.Prune (Mask readSchedule renameFlow renameWires)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {out : ValueSort Data} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable (p : Program src entry)

/-- In order: the latch condition, the return value and the simultaneous
feedback bank used at the checked θ boundary. -/
abbrev packetPorts (out : ValueSort Data) (carry : Mask regs) : List (Ty Data) :=
  .value .predicate :: .value out :: dataPorts carry.kept

def observe {F : Ty Data → Type w} (carry : Mask regs) (bank : Tuple F (dataPorts regs)) :
    Tuple F (packetPorts out carry) :=
  .cons (bank.get p.again) (.cons (bank.get p.result) (carry.project bank))

def transfer := headerTransferFor (Nested.Numbered.tail p)

/-- The final versions are resolved after the ordered merge and latch
quads. A test or carried slot overwritten in those blocks uses its new
producer, not the version that entered the merge. -/
def outgoing (carry : Mask regs) :
    Wires (dataPorts regs) (extend [] (Nested.Numbered.tail p).producers) (packetPorts out carry) :=
  observe p carry (transfer p).outgoing

/-- The backward sweep keeps every scheduled producer's operands, using
only the actual latch packet as the final set of reads. -/
def mergeMask (carry : Mask regs) : Mask regs :=
  let reads := readSchedule (transfer p).flow ++ [(outgoing p carry).addresses]
  let live := RVSDG.NestedTheta.Liveness.sweep reads 0
  Mask.ofSlots (fun i => live.contains (.arg i)) regs

structure Checked (p : Program src entry) (carry merge : Mask regs) where
  flow : Dataflow Op (dataPorts merge.kept) [] (Nested.Numbered.tail p).producers
  packet : Wires (dataPorts merge.kept) (extend [] (Nested.Numbered.tail p).producers) (packetPorts out carry)
  smaller : merge.kept.length < regs.length
  flow_eq : renameFlow merge.rename (transfer p).flow = some flow
  packet_eq : renameWires merge.rename (outgoing p carry) = some packet

def checkMask (carry merge : Mask regs) : Option (Checked p carry merge) :=
  if smaller : merge.kept.length < regs.length then
    match flow_eq : renameFlow merge.rename (transfer p).flow,
          packet_eq : renameWires merge.rename (outgoing p carry) with
    | some flow, some packet => some ⟨flow, packet, smaller, flow_eq, packet_eq⟩
    | _, _ => none
  else none

def prune (carry : Mask regs) : Option (Checked p carry (mergeMask p carry)) :=
  checkMask p carry (mergeMask p carry)

def Checked.eval {p : Program src entry} {carry merge : Mask regs} (checked : Checked p carry merge)
    (m : Model.{u, v, w} Op) (input : Bank (regs := merge.kept) m) : Tuple (Val m.value) (packetPorts out carry) :=
  checked.packet.read input (checked.flow.eval m input PUnit.unit)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch
