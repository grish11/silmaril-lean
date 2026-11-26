module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Preservation
import Silmaril.Proofs.Wasm.Institution.Operational.HostCall.Lime1.Indirect

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

/-- Resolution consumes the selector in one internal step and preserves the
current store, frame, operands and suffix. Success leaves a pending host or
checked Wasm invocation. Bounds, null and signature failures leave a native trap. -/
theorem IndirectSite.step_iff {indirect : IndirectSite} {active : Frame} {stack : List Value}
    {selector : BitVec 32} {rest : List Admin} (linked : indirect.Linked base active.module) :
    Internal ⟨memory.store bytes, active,
      values (stack ++ [Value.int .i32 selector]) ++ .source (.callIndirect indirect.typeIndex) :: rest⟩ dst ↔
      ∃ target, indirect.Lookup base selector target ∧
        dst = ⟨memory.store bytes, active, values stack ++ IndirectSite.lookupHead target :: rest⟩ :=
  Proofs.indirect_step_iff linked

/-- Each witnessed lookup failure has only the trap successor, with the
current store and remaining operands unchanged. -/
theorem IndirectSite.trap_iff {indirect : IndirectSite} {active : Frame} {stack : List Value}
    {selector : BitVec 32} {rest : List Admin} (linked : indirect.Linked base active.module)
    (failure : indirect.Lookup base selector none) :
    Internal ⟨memory.store bytes, active,
      values (stack ++ [Value.int .i32 selector]) ++ .source (.callIndirect indirect.typeIndex) :: rest⟩ dst ↔
      dst = ⟨memory.store bytes, active, values stack ++ .trap :: rest⟩ :=
  Proofs.indirect_trap_iff linked failure

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1
