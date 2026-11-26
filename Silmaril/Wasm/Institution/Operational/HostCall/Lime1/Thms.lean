module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Preservation

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1

open Execution.Runtime (EvalCtx Frame Value)
open Wasm.Lime1.Execution

variable {H : Type} {base : Store H} {host : HostSemantics H}
  {memory : Memory32 base} {site : Site H} {outer : Frame} {context : EvalCtx Wasm.Lime1.Instr}
  {args : List Value} {bytes : ByteArray} {dst : Config H}

theorem Memory32.store_initial : memory.store memory.initial.data = base :=
  Proofs.store_initial

/-- All native answers preserve the checked live-store representation under
the embedding contract. A returned trap carries its returned bytes. A declared
divergence has the native self-step, and absence of any answer gives no step. -/
theorem Site.step_iff (allocated : site.Allocated base) (contract : site.Contract memory host)
    (live : memory.Live bytes) (typed : site.Arguments args) :
    Step host (site.pending (memory.store bytes) outer context args) dst ↔
      (∃ next outcome, memory.Live next ∧ site.TypedResult outcome ∧
        host site.code (memory.store bytes) args (.returned (memory.store next) outcome) ∧
        dst = ⟨memory.store next, outer, context.plug value (result outcome)⟩) ∨
      (host site.code (memory.store bytes) args .diverged ∧
        dst = site.pending (memory.store bytes) outer context args) :=
  Proofs.step_iff allocated contract live typed

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1
