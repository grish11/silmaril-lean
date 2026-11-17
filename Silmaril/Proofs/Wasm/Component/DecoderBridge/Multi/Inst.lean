module

public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.LaterCore
public import Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi.FirstK2

/-!
# The instantiation on `MultiImpFrag` (pieces (b) and (c))

`nodesRef : Task.nodesRef`, from the first node with its finishing continuation, the machine
invariant and the frame related to the symbolic reading (`FirstK2.firstK'`), a later core
instantiation in the shared core store (`LaterCore.laterCoreStep'`), and the other definitions
and the end of the instantiation (`Nodes.nodesRef_of'`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi

/-- **The instantiation on the fragment, by unique steps.** -/
theorem nodesRefL : NodesRefL :=
  nodesRefL_of' firstK' laterCoreStep'

/-- **The instantiation on the fragment.** -/
theorem nodesRef : Silmaril.Wasm.Component.DecoderBridge.Task.nodesRef :=
  nodesRef_of' firstK' laterCoreStep'

end Silmaril.Proofs.Wasm.Component.DecoderBridge.Multi
