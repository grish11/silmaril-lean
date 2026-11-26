module

public import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Defs
import Silmaril.Wasm.Institution.Operational.MemoryWrite.Native.Thms
import Silmaril.Wasm.Institution.Operational.MemoryQuery.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.MemoryWrite.Proofs.Lime1Context

open Execution.Runtime (Frame MemAddr MemInst Value)
open Wasm.Lime1.Execution

private theorem internal_of_absent {H : Type} {host : HostSemantics H} {src dst : Config H}
    (absent : decompose? src = none) : Step host src dst ↔ Internal src dst :=
  Step.internal_iff_of_not_callout (fun _ call => by
    obtain ⟨_, found, _⟩ := decompose?_complete call
    simp [absent] at found)

theorem load_step_iff {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg} {ptr : BitVec 32}
    {saved : List Value} {tail : List Admin} {dst : Config H}
    (lookup : frameMemory s f = some (a, m)) :
    Step host ⟨s, f, values saved ++ MemoryQuery.limeCodeAt immediate (.load ptr) ++ tail⟩ dst ↔
      ∃ out, MemoryQuery.EdgeAt m.data immediate.offset.val (.load ptr) out ∧
        dst = ⟨s, f, values saved ++ MemoryQuery.limeCodeAt immediate out ++ tail⟩ := by
  constructor
  · intro move
    have absent : decompose? (⟨s, f, values saved ++ MemoryQuery.limeCodeAt immediate (.load ptr) ++ tail⟩ :
        Config H) = none := by simp [decompose?, MemoryQuery.limeCodeAt, asValue?]
    have step := (internal_of_absent absent).mp move
    have shape : values saved ++ MemoryQuery.limeCodeAt immediate (.load ptr) ++ tail =
        values (saved ++ [Value.int .i32 ptr]) ++ .source (.intLoad .i32 none immediate) :: tail := by
      simp [MemoryQuery.limeCodeAt, values, value, Value.int]
    rw [shape] at step
    obtain ⟨mid, load, rfl⟩ := CallContinuation.lime_intLoad_strip step
    obtain ⟨out, edge, rfl⟩ := (MemoryQuery.lime_step_iff_at immediate lookup (query := .load ptr)).mp load
    exact ⟨out, edge, rfl⟩
  · rintro ⟨out, edge, rfl⟩
    exact .context (MemoryQuery.lime_sound_at immediate lookup edge) saved tail

theorem store_step_iff {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
    {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg} {ptr word : BitVec 32}
    {saved : List Value} {tail : List Admin} {dst : Config H}
    (lookup : frameMemory s f = some (a, m)) :
    Step host ⟨s, f, values saved ++ (limeConfigAt immediate s f a m (.store ptr word)).code ++ tail⟩ dst ↔
      ∃ out, EdgeAt m.data immediate.offset.val (.store ptr word) out ∧
        let next := limeConfigAt immediate s f a m out
        dst = ⟨next.store, next.frame, values saved ++ next.code ++ tail⟩ := by
  constructor
  · intro move
    have absent : decompose? (⟨s, f, values saved ++
        (limeConfigAt immediate s f a m (.store ptr word)).code ++ tail⟩ : Config H) = none := by
      simp [decompose?, limeConfigAt, asValue?]
    have step := (internal_of_absent absent).mp move
    have shape : values saved ++ (limeConfigAt immediate s f a m (.store ptr word)).code ++ tail =
        values (saved ++ [Value.int .i32 ptr, Value.int .i32 word]) ++
          .source (.intStore .i32 none immediate) :: tail := by
      simp [limeConfigAt, values, value, Value.int]
    rw [shape] at step
    obtain ⟨mid, write, rfl⟩ := CallContinuation.lime_intStore_strip step
    obtain ⟨out, edge, rfl⟩ := (lime_step_iff_at immediate lookup (a := .store ptr word)).mp write
    exact ⟨out, edge, rfl⟩
  · rintro ⟨out, edge, rfl⟩
    exact .context (lime_sound_at immediate lookup edge) saved tail

private theorem activation_iff {H : Type} {host : HostSemantics H} {s : Store H}
    {caller callee : Frame} {arity : Nat} {saved : List Value} {tail body : List Admin} {dst : Config H}
    (absent : Execution.Runtime.decomposeFrom? coding s [] body = none)
    (stays : ∀ out, ¬ PureStep callee.module.types [.label arity [] body] out) :
    Step host ⟨s, caller, limeActivationCode arity callee saved tail body⟩ dst ↔
      ∃ mid, Step host ⟨s, callee, body⟩ mid ∧
        dst = ⟨mid.store, caller, limeActivationCode arity mid.frame saved tail mid.code⟩ := by
  constructor
  · intro move
    have noCall : decompose? (⟨s, caller, limeActivationCode arity callee saved tail body⟩ :
        Config H) = none := by simp [decompose?, limeActivationCode, absent]
    obtain ⟨mid, inner, rfl⟩ := CallContinuation.lime_frame_context_inv ((internal_of_absent noCall).mp move)
    rcases CallContinuation.OuterCall.Computed.lime_body_step_cases inner with
      ⟨next, step, rfl⟩ | ⟨out, pop, _⟩
    · exact ⟨next, Step.of_internal step, by simp [limeActivationCode, List.append_assoc]⟩
    · exact (stays out pop).elim
  · rintro ⟨mid, move, rfl⟩
    simpa only [limeActivationCode, List.append_assoc, List.singleton_append] using
      Step.context (Step.frame (Step.label move arity []) arity caller) saved tail

theorem load_activation_iff {H : Type} {host : HostSemantics H} {s : Store H}
    {caller callee : Frame} {arity : Nat} {callerSaved saved : List Value} {callerTail tail : List Admin}
    {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg} {ptr : BitVec 32}
    {dst : Config H} (lookup : frameMemory s callee = some (a, m)) :
    Step host ⟨s, caller, limeActivationCode arity callee callerSaved callerTail
      (values saved ++ MemoryQuery.limeCodeAt immediate (.load ptr) ++ tail)⟩ dst ↔
      ∃ out, MemoryQuery.EdgeAt m.data immediate.offset.val (.load ptr) out ∧
        dst = ⟨s, caller, limeActivationCode arity callee callerSaved callerTail
          (values saved ++ MemoryQuery.limeCodeAt immediate out ++ tail)⟩ := by
  have shape : values saved ++ MemoryQuery.limeCodeAt immediate (.load ptr) ++ tail =
      values (saved ++ [Value.int .i32 ptr]) ++ .source (.intLoad .i32 none immediate) :: tail := by
    simp [MemoryQuery.limeCodeAt, values, value, Value.int]
  rw [activation_iff (by simp [shape, asValue?]) (fun out pop => ?_)]
  · constructor
    · rintro ⟨mid, move, rfl⟩
      obtain ⟨out, edge, rfl⟩ := (load_step_iff lookup).mp move
      exact ⟨out, edge, rfl⟩
    · rintro ⟨out, edge, rfl⟩
      exact ⟨_, (load_step_iff lookup).mpr ⟨out, edge, rfl⟩, rfl⟩
  · rw [shape] at pop
    exact CallContinuation.OuterCall.Computed.lime_label_stays rfl (by simp) (by simp) (by simp) pop

theorem store_activation_iff {H : Type} {host : HostSemantics H} {s : Store H}
    {caller callee : Frame} {arity : Nat} {callerSaved saved : List Value} {callerTail tail : List Admin}
    {a : MemAddr} {m : MemInst} {immediate : Wasm.V1.MemArg} {ptr word : BitVec 32}
    {dst : Config H} (lookup : frameMemory s callee = some (a, m)) :
    Step host ⟨s, caller, limeActivationCode arity callee callerSaved callerTail
      (values saved ++ (limeConfigAt immediate s callee a m (.store ptr word)).code ++ tail)⟩ dst ↔
      ∃ out, EdgeAt m.data immediate.offset.val (.store ptr word) out ∧
        let next := limeConfigAt immediate s callee a m out
        dst = ⟨next.store, caller, limeActivationCode arity next.frame callerSaved callerTail
          (values saved ++ next.code ++ tail)⟩ := by
  have shape : values saved ++ (limeConfigAt immediate s callee a m (.store ptr word)).code ++ tail =
      values (saved ++ [Value.int .i32 ptr, Value.int .i32 word]) ++
        .source (.intStore .i32 none immediate) :: tail := by
    simp [limeConfigAt, values, value, Value.int]
  rw [activation_iff (by simp [shape, asValue?]) (fun out pop => ?_)]
  · constructor
    · rintro ⟨mid, move, rfl⟩
      obtain ⟨out, edge, rfl⟩ := (store_step_iff lookup).mp move
      exact ⟨out, edge, rfl⟩
    · rintro ⟨out, edge, rfl⟩
      exact ⟨_, (store_step_iff lookup).mpr ⟨out, edge, rfl⟩, rfl⟩
  · rw [shape] at pop
    exact CallContinuation.OuterCall.Computed.lime_label_stays rfl (by simp) (by simp) (by simp) pop

end Silmaril.Wasm.Institution.Operational.MemoryWrite.Proofs.Lime1Context
