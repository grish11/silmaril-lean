module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.V1.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.V1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect

open Execution.Runtime (Frame Value)
open Wasm.V1.Execution

/-- The lookup step consumes only the unsigned i32 selector. The resulting
invocation or trap retains the prefix, continuation, caller and entire store. -/
theorem v1_step_iff {H : Type} {host : HostSemantics H} {s : Store H} {caller : Frame}
    {index : TypeIdx} {selector : BitVec 32} {stack : List Value} {tail : List Admin} {dst : Config H} :
    Step host (v1Source s caller index selector stack tail) dst ↔
      ∃ out, v1Resolve s caller index selector = some out ∧ dst = v1Resolved s caller stack tail out :=
  Proofs.V1.step_iff

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect
