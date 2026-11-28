module

public import Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Defs

/-! Provenance of addresses in the ordered native memory profile. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.AddressProvenance

open Memory.DeadStore.Search.Selection.Readers.Repeat (Operation)

/-- The scalar scopes reachable from Start. A Store leaves the scope
unchanged, and a Load adds exactly one word port. -/
inductive LoadScope : List (List ValueSort) → Prop where
  | start : LoadScope []
  | load {past : List (List ValueSort)} : LoadScope past → LoadScope ([.word] :: past)

variable {args : List ValueSort}

/-- Each memory access carries the exact argument port that it reads or writes. -/
def ArgumentAddress : Operation args → Prop
  | .ret _ => True
  | .load address | .store address _ => ∃ port, address = .arg port

end Silmaril.SSA.SeaOfNodes.Memory.AddressProvenance
