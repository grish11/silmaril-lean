module

public import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.Deletion.Defs

/-! Checked deletion of one nominated binding in a pure acyclic table
with an ordered packet of outgoing uses. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Pure.Deletion

open Diamond (Dataflow Signature Ty ValueSort)
open GVN (Producer)
open GVN.Cyclic.Deletion (Erasure Route erase?)
open RVSDG (Wires extend)

universe u v

variable {Data : Type u} {Op : Signature.{u,v} Data}
variable {args ports : List (Ty Data)} {past sigs : List (List (Ty Data))}
variable {out : ValueSort Data} {flow : Dataflow Op args past sigs}

/-- The outgoing packet may contain return, guard or branch-argument
wires. The client supplies all outgoing reads of this table. -/
structure Result (Op : Signature.{u,v} Data) (args ports : List (Ty Data))
    (past sigs : List (List (Ty Data))) where
  erasure : Erasure Op args past sigs
  outputs : Wires args (extend past erasure.sigs') ports

/-- Check all surviving operands, then reindex every outgoing occurrence
with the same partial map. A read of the removed result fails the check. -/
def delete? (candidate : Producer flow out) (outputs : Wires args (extend past sigs) ports) :
    Option (Result Op args ports past sigs) :=
  (erase? candidate).bind fun erasure =>
    (Route.wires? erasure.route outputs).map fun mapped => ⟨erasure, mapped⟩

/-- Exact opcodes with their ordered input profile and output sort. -/
def opcodes : {past sigs : List (List (Ty Data))} → Dataflow Op args past sigs →
    List (Σ ins out, Op ins out)
  | _, _, .nil => []
  | _, _, .cons (ins := ins) (out := out) op _ rest => ⟨ins, out, op⟩ :: opcodes rest

/-- The nomination's zero-based position relative to the start of this table. -/
def position : {past sigs : List (List (Ty Data))} → {flow : Dataflow Op args past sigs} →
    {out : ValueSort Data} → Producer flow out → Nat
  | _, _, _, _, .here => 0
  | _, _, _, _, .later candidate => (position candidate).succ

end Silmaril.SSA.SeaOfNodes.Pure.Deletion
