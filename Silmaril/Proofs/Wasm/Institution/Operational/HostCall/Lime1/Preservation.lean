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

theorem answer_through {inner wrapped : Config H} {call : Execution.Runtime.Callout H Wasm.Lime1.Instr}
    (plugged : wrapped.code = context.plug value inner.code) (store : wrapped.store = inner.store)
    (present : (decompose? wrapped).isSome = (decompose? inner).isSome)
    (located : CalloutAt wrapped call) (answer : Answer host wrapped call dst) :
    ∃ c mid, CalloutAt inner c ∧ Answer host inner c mid ∧
      dst = ⟨mid.store, wrapped.frame, context.plug value mid.code⟩ := by
  cases found : decompose? inner with
  | none =>
    have reachable := exists_callout_iff.mp ⟨call, located⟩
    simp [present, found] at reachable
  | some c =>
    have here := decompose?_sound found
    have lifted : CalloutAt wrapped { c with context := context.comp c.context } := by
      refine ⟨?_, store ▸ here.found, here.arity⟩
      change wrapped.code = (context.comp c.context).plug value (c.redex coding)
      rw [plugged, EvalCtx.plug_comp]
      congr 1
      exact here.plugged
    obtain ⟨_, _, hostEq, argsEq, resumes⟩ := located.unique lifted
    rcases Answer.iff.mp answer with ⟨returned, outcome, behavior, eq⟩ | ⟨diverged, rfl⟩
    · have inside : host c.host inner.store c.args (.returned returned outcome) := by
        simpa only [store, hostEq, argsEq] using behavior
      refine ⟨c, resume inner c returned outcome, here, .returned returned outcome inside, ?_⟩
      rw [eq, resumes]
      simp [resume, Execution.Runtime.Callout.fill, EvalCtx.plug_comp]
    · have inside : host c.host inner.store c.args .diverged := by
        simpa only [store, hostEq, argsEq] using diverged
      exact ⟨c, inner, here, .diverged inside, by cases dst; simp_all⟩

theorem answer_under {inner wrapped : Config H} {call : Execution.Runtime.Callout H Wasm.Lime1.Instr}
    (plugged : wrapped.code = context.plug value inner.code) (store : wrapped.store = inner.store)
    (decomposed : decompose? wrapped = (decompose? inner).map
      (fun c => { c with context := context.comp c.context }))
    (located : CalloutAt wrapped call) (answer : Answer host wrapped call dst) :
    ∃ c mid, CalloutAt inner c ∧ Answer host inner c mid ∧
      dst = ⟨mid.store, wrapped.frame, context.plug value mid.code⟩ := by
  apply answer_through plugged store _ located answer
  rw [decomposed]
  cases decompose? inner <;> rfl

theorem memoryLinked_forFiniteRun {indirect : IndirectSite}
    {calls : CallContinuation.OuterCall.Ranked.Graph.Memory32.CallMode}
    (linked : indirect.MemoryLinked memory host calls) : indirect.MemoryLinked memory host .recursive := by
  refine ⟨linked.checked, ?_, ?_⟩
  · intro parent registered target used
    rcases linked.direct parent registered target used with ⟨child, link, _⟩ | hostLink
    · exact .inl ⟨child, link, trivial⟩
    · exact .inr hostLink
  · intro parent registered index signature used
    have link := linked.indirect parent registered index signature used
    refine ⟨link.tableAt, link.signatureAt, fun address member => ?_⟩
    obtain ⟨fn, allocated, matched⟩ := link.entries address member
    refine ⟨fn, allocated, fun typed => ?_⟩
    cases fn with
    | host => exact matched typed
    | wasm =>
      obtain ⟨child, found, childAllocated, _⟩ := matched typed
      exact ⟨child, found, childAllocated, trivial⟩

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.Proofs
