module

public import Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Defs

/-! Derive reflexive static Store contracts from the entry's typed operands. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference

open RVSDG (Port Tuple)
open Memory.DeadStore.Search.Selection.Readers.Repeat (operations)

variable {args : List ValueSort} {cells : Nat}

/-- One contract per Store address argument, in first occurrence order.
The checker already recognizes the anchor port as a must-alias. All
other ports remain unclassified. -/
def inferContracts (entry : Memory.Graph args) : List (AddressContract args) :=
  let ports : List (Port args .address) := (operations entry).filterMap fun
    | .store (.arg port) _ => some port
    | _ => none
  (ports.eraseDupsBy (fun first second => first.index == second.index)).map
    (fun port => ⟨⟨port, []⟩, []⟩)

/-- Use the existing discovery and emission API with facts inferred from
the entry alone. The invocation supplies the scalar input for the emitted pair. -/
def lower (graph : Graph args) (entry : Memory.Graph args) (input : Tuple (Val cells) args) :
    Except Search.InvocationError (Search.Emission cells args) :=
  Search.lower graph entry (inferContracts entry) input

end Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Entry.Composition.Retained.Load.Static.Sequence.Search.Inference
