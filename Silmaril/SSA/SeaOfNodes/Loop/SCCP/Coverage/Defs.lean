module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Defs

/-! Decide entry coverage using the existing typed bank equality. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP

open SeaOfNodes.Diamond (Ty Val)
open SeaOfNodes.Diamond.SCCP (Fact TupleCovers)
open Semantics.Dataflow (Flat)
open RVSDG (Tuple)

universe u w

def decideFactCovers {α : Type w} [DecidableEq α] (fact : Flat α) (actual : α) :
    Decidable (fact.Covers actual) :=
  match fact with
  | .bottom => .isFalse id
  | .constant expected => inferInstanceAs (Decidable (expected = actual))
  | .overdefined => .isTrue trivial

/-- Decide the actual portwise coverage relation. Traverse the typed bank
in order and stop at the first fact that does not cover its entry value. -/
def decideTupleCovers {Data : Type u} {value : Data → Type w} :
    {ports : List (Ty Data)} → [BankDecidableEq value ports] →
    (facts : Tuple (Fact value) ports) → (input : Tuple (Val value) ports) →
    Decidable (TupleCovers facts input)
  | [], _, .nil, .nil => .isTrue (fun port => nomatch port)
  | _ :: rest, equal, .cons fact facts, .cons actual input =>
    match @decideFactCovers _ (equal.atPort 0) fact actual with
    | .isFalse incompatible => .isFalse (fun covers => incompatible (covers .head))
    | .isTrue head =>
      letI : BankDecidableEq value rest := ⟨fun i => equal.atPort i.succ⟩
      match decideTupleCovers facts input with
      | .isFalse incompatible => .isFalse (fun covers => incompatible (fun port => covers (.tail port)))
      | .isTrue tail => .isTrue (fun port => match port with
        | .head => head
        | .tail port => tail port)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP
