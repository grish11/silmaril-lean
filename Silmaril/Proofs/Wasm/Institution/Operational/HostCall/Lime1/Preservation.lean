module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Defs
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Proofs

open Execution.Runtime (EvalCtx Frame Value)
open Wasm.Lime1.Execution

variable {H : Type} {base : Store H} {host : HostSemantics H}
  {memory : Memory32 base} {site : Site H} {outer : Frame} {context : EvalCtx Wasm.Lime1.Instr}
  {args : List Value} {bytes : ByteArray} {dst : Config H}

theorem store_initial : memory.store memory.initial.data = base := by
  obtain ⟨inBounds, found⟩ := List.getElem_of_getElem? memory.allocated
  have memories : base.memories.set memory.address.value memory.initial = base.memories := by
    rw [← found, List.set_getElem_self inBounds]
  change { base with memories := base.memories.set memory.address.value memory.initial } = base
  rw [memories]

theorem pending_iff (allocated : site.Allocated base) (typed : site.Arguments args) :
    Step host (site.pending (memory.store bytes) outer context args) dst ↔
      (∃ returned outcome, host site.code (memory.store bytes) args (.returned returned outcome) ∧
        dst = ⟨returned, outer, context.plug value (result outcome)⟩) ∨
      (host site.code (memory.store bytes) args .diverged ∧
        dst = site.pending (memory.store bytes) outer context args) := by
  have located : CalloutAt (site.pending (memory.store bytes) outer context args) (site.callout context args) :=
    ⟨rfl, allocated, by simpa [Site.callout] using congrArg List.length typed⟩
  exact located.step_iff.trans Answer.iff

theorem step_iff (allocated : site.Allocated base) (contract : site.Contract memory host)
    (live : memory.Live bytes) (typed : site.Arguments args) :
    Step host (site.pending (memory.store bytes) outer context args) dst ↔
      (∃ next outcome, memory.Live next ∧ site.TypedResult outcome ∧
        host site.code (memory.store bytes) args (.returned (memory.store next) outcome) ∧
        dst = ⟨memory.store next, outer, context.plug value (result outcome)⟩) ∨
      (host site.code (memory.store bytes) args .diverged ∧
        dst = site.pending (memory.store bytes) outer context args) := by
  rw [pending_iff allocated typed]
  constructor
  · rintro (⟨returned, outcome, behavior, rfl⟩ | diverged)
    · obtain ⟨next, nextLive, rfl, valid⟩ := contract live typed behavior
      exact .inl ⟨next, outcome, nextLive, valid, behavior, rfl⟩
    · exact .inr diverged
  · rintro (⟨next, outcome, _, _, behavior, rfl⟩ | diverged)
    · exact .inl ⟨memory.store next, outcome, behavior, rfl⟩
    · exact .inr diverged

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Proofs
