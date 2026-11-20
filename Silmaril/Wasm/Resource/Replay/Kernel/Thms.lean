module

public import Silmaril.Wasm.Resource.Replay.Kernel.Defs
import Silmaril.Proofs.Wasm.Resource.Replay.Kernel

@[expose] public section

namespace Silmaril.Wasm.Resource.Replay.Kernel

open Silmaril.Wasm.Game

/-- The structural, kernel-facing driver computes the verified replay at every call bound. -/
theorem replayFromK_eq (inst : ScalarInstance) (script : Script) (fuel count : Nat) :
    replayFromK inst script fuel count = replayFrom inst script fuel count :=
  Silmaril.Proofs.Wasm.Resource.Replay.Kernel.replayFromK_eq inst script fuel count

end Silmaril.Wasm.Resource.Replay.Kernel
