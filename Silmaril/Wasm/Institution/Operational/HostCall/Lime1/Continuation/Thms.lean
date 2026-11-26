module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Preservation
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Continuation.Readback

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation

open Execution.Runtime (Frame)
open Wasm.Lime1.Execution

variable {H : Type} {base : Store H} {mem : Memory32 base} {host : HostSemantics H}
  {outer active : Frame} {results : List NumType} {a b : State H} {dst : Config H}

/-- Every edge preserves live memory and the typing of the remaining code or
the returned results. The active frame is fixed until native restoration. -/
theorem preserves (move : Edge mem host active results a b)
    (ready : Ready mem host active results a.phase a.labels) (live : mem.Live a.bytes) :
    Ready mem host active results b.phase b.labels ∧ mem.Live b.bytes :=
  ⟨Proofs.ready_step move ready, Proofs.live_step move live⟩

/-- Exact single-step correspondence for a checked continuation under any finite
stack of entered labels and its function frame. The native i32 selection
and the selected block's ordered parameter delivery are separate steps.
Normal label exit delivers the declared result stack to the saved prefix.
A direct or taken conditional branch crosses one intervening label per native
step. The target transfer delivers the ordered results and discards the
target's remaining instructions. A function-label target leaves a value-only
frame for the subsequent native caller-restoration step. -/
theorem step_iff (ready : Ready mem host active results a.phase a.labels) (live : mem.Live a.bytes) :
    Step host (render mem outer active results a) dst ↔
      ∃ next, Edge mem host active results a next ∧ dst = render mem outer active results next :=
  Proofs.step_iff ready live

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Continuation
