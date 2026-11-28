module

public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32.Run.Defs
public import Silmaril.Wasm.Institution.Operational.HostCall.V1.Defs

/-!
# Store effects at a V1 host return

The graph renders the whole store from a fixed allocation and one live byte
array. A host return can rejoin this representation when the embedding proves
the corresponding update from the actual input store.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32

open Execution.Runtime (MemAddr MemInst)
open Wasm.V1.Execution

/-- Update the live memory at its existing address and declared limit.
The fixed profile preserves its extent. The growing profile compares with
the current extent and keeps the page bounds. Returned traps use this same
store relation. -/
def HostStoreEffect {H : Type} (mode : MemoryMode) (address : MemAddr) (initial : MemInst)
    (before after : Store H) : Prop :=
  ∃ prior next : ByteArray,
    before.memories[address.value]? = some { initial with data := prior } ∧
    mode.extent prior.size next ∧ after = storeWithBytes before address initial next

end Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Memory32
