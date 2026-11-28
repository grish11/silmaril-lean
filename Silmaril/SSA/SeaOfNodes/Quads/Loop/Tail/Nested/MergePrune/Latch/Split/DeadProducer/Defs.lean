module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.Defs
public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Pass.Defs
public import Silmaril.SSA.SeaOfNodes.Pure.Deletion.Iteration.Defs

/-! # Delete a pure producer from a checked merge–latch transfer -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.DeadProducer

open SeaOfNodes.Diamond (Model Ty Val ValueSort dataPorts)
open SeaOfNodes.GVN (Producer)
open SeaOfNodes.GVN.Cyclic.Deletion (Erasure Route erase?)
open SeaOfNodes.Pure.Deletion.Iteration (Table)
open RVSDG (Tuple Wires extend)
open Join (Block)
open Blocks (Bank)
open Blocks.Prune (Mask)

universe u v w

variable {Data : Type u} {Op : SeaOfNodes.Diamond.Signature.{u, v} Data}
variable {regs : List (ValueSort Data)} {body : Block Op regs} {mask : Mask regs}
variable {outputs : List (Ty Data)} {wires : Wires (dataPorts regs) (extend [] body.producers) outputs}

/-- Keep the argument and packet interfaces while removing one binding
from the checked, already renamed producer table. -/
structure Checked (transfer : Transfer body mask wires) where
  sort : ValueSort Data
  candidate : Producer transfer.flow sort
  erased : Erasure Op (dataPorts mask.kept) [] body.producers
  outgoing : Wires (dataPorts mask.kept) (extend [] erased.sigs') outputs
  erased_eq : erase? candidate = some erased
  outgoing_eq : Route.wires? erased.route transfer.outgoing = some outgoing

/-- The iteration starts at the actual checked table, with its entire packet. -/
def originalTable (transfer : Transfer body mask wires) : Table Op (dataPorts mask.kept) outputs :=
  ⟨body.producers, transfer.flow, transfer.outgoing⟩

def Checked.table {transfer : Transfer body mask wires} (cut : Checked transfer) :
    Table Op (dataPorts mask.kept) outputs :=
  ⟨cut.erased.sigs', cut.erased.flow, cut.outgoing⟩

/-- Erasure checks every operand of every surviving producer, in scope
order, then checks all the outgoing reads. Failure refuses the cut. -/
def check (transfer : Transfer body mask wires) {sort : ValueSort Data}
    (candidate : Producer transfer.flow sort) : Option (Checked transfer) :=
  match erased_eq : erase? candidate with
  | none => none
  | some erased =>
    match outgoing_eq : Route.wires? erased.route transfer.outgoing with
    | none => none
    | some outgoing => some ⟨sort, candidate, erased, outgoing, erased_eq, outgoing_eq⟩

/-- Select the first successful single deletion in the existing producer order. -/
def first (transfer : Transfer body mask wires) : Option (Checked transfer) :=
  (SeaOfNodes.GVN.Cyclic.Pass.producers transfer.flow).findSome? fun ⟨_, producer⟩ => check transfer producer

def Checked.eval {transfer : Transfer body mask wires} (cut : Checked transfer)
    (m : Model.{u, v, w} Op) (input : Bank (regs := mask.kept) m) : Tuple (Val m.value) outputs :=
  cut.outgoing.read input (cut.erased.flow.eval m input PUnit.unit)

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Split.DeadProducer
