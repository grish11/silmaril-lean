module

public import Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Defs
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms
import Silmaril.Wasm.Institution.Operational.Loops.Indexed.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Proofs

set_option backward.isDefEq.respectTransparency false

open Execution.Runtime (AdminInstr Frame Value)
open Wasm.Lime1.Execution
open CallContinuation
open CallContinuation.OuterCall

variable {H : Type} {p : Program H} {base : Store H} {mem : Memory32 base}
  {outer : Frame} {index : FuncIdx} {arg : BitVec 64} {bytes : ByteArray} {dst : Config H}

private theorem stay {f : Frame} {n : Nat} {cont : Wasm.Lime1.Expr}
    {saved : List Value} {head : Admin} {tail out : List Admin}
    (nonvalue : asValue? head = none) (notBranch : ∀ i, head ≠ .source (.br i))
    (notReturn : head ≠ .source .return_) (notFinalTrap : head = .trap → saved ≠ [] ∨ tail ≠ []) :
    ¬ PureStep f.module.types [.label n cont (values saved ++ head :: tail)] out :=
  Computed.lime_label_stays nonvalue notBranch notReturn notFinalTrap

private theorem function_context {s : Store H} {code : List Admin}
    (stays : ∀ out, ¬ PureStep (p.active arg).module.types [.label p.functionResults.length [] code] out) :
    Internal ⟨s, outer, p.functionCode arg code⟩ dst ↔
      ∃ mid, Internal ⟨s, p.active arg, code⟩ mid ∧
        dst = ⟨mid.store, outer, [.frame p.functionResults.length mid.frame [.label p.functionResults.length [] mid.code]]⟩ := by
  constructor
  · intro step
    rcases Computed.lime_body_step_cases step with inside | ⟨out, pop, _⟩
    · exact inside
    · exact (stays out pop).elim
  · rintro ⟨mid, step, rfl⟩
    exact .frame (.label step p.functionResults.length []) p.functionResults.length outer

private theorem function_iff {s : Store H} {code next : List Admin}
    (stays : ∀ out, ¬ PureStep (p.active arg).module.types [.label p.functionResults.length [] code] out)
    (localStep : ∀ {mid}, Internal ⟨s, p.active arg, code⟩ mid ↔ mid = ⟨s, p.active arg, next⟩) :
    Internal ⟨s, outer, p.functionCode arg code⟩ dst ↔ dst = ⟨s, outer, p.functionCode arg next⟩ := by
  rw [function_context stays]
  constructor
  · rintro ⟨_, step, rfl⟩
    obtain rfl := localStep.mp step
    rfl
  · rintro rfl
    exact ⟨_, localStep.mpr rfl, rfl⟩

private theorem loop_context {s : Store H} {code : List Admin}
    (stays : ∀ out, ¬ PureStep (p.active arg).module.types [.label 1 [p.loop.instr] code] out) :
    Internal ⟨s, outer, p.functionCode arg (p.loopCode code)⟩ dst ↔
      ∃ mid, Internal ⟨s, p.active arg, code⟩ mid ∧
        dst = ⟨mid.store, outer, [.frame p.functionResults.length mid.frame [.label p.functionResults.length [] (p.loopCode mid.code)]]⟩ := by
  have fnStays (out : List Admin) :
      ¬ PureStep (p.active arg).module.types [.label p.functionResults.length [] (p.loopCode code)] out :=
    stay (saved := [i64 p.saved]) rfl (by simp) (by simp) (by simp)
  rw [function_context fnStays]
  have invert {target : Config H} :=
    Blocks.Context.lime_label_cont_iff (s := s) (f := p.active arg) (saved := [i64 p.saved])
      (n := 1) (cont := [p.loop.instr]) (body := code) (rest := p.afterLoop) (dst := target)
  constructor
  · rintro ⟨mid, step, rfl⟩
    rcases invert.mp step with ⟨inside, innerStep, rfl⟩ | ⟨out, pop, _⟩
    · exact ⟨inside, innerStep, rfl⟩
    · exact (stays out pop).elim
  · rintro ⟨mid, step, rfl⟩
    exact ⟨_, invert.mpr (.inl ⟨mid, step, rfl⟩), rfl⟩

private theorem loop_iff {s : Store H} {code next : List Admin}
    (stays : ∀ out, ¬ PureStep (p.active arg).module.types [.label 1 [p.loop.instr] code] out)
    (localStep : ∀ {mid}, Internal ⟨s, p.active arg, code⟩ mid ↔ mid = ⟨s, p.active arg, next⟩) :
    Internal ⟨s, outer, p.functionCode arg (p.loopCode code)⟩ dst ↔
      dst = ⟨s, outer, p.functionCode arg (p.loopCode next)⟩ := by
  rw [loop_context stays]
  constructor
  · rintro ⟨_, step, rfl⟩
    obtain rfl := localStep.mp step
    rfl
  · rintro rfl
    exact ⟨_, localStep.mpr rfl, rfl⟩

private theorem loop_trap_exit {s : Store H} :
    Internal ⟨s, p.active arg, p.loopCode [.trap]⟩ dst ↔
      dst = ⟨s, p.active arg, value (i64 p.saved) :: .trap :: p.afterLoop⟩ := by
  have invert :=
    Blocks.Context.lime_label_cont_iff (s := s) (f := p.active arg) (saved := [i64 p.saved])
      (n := 1) (cont := [p.loop.instr]) (body := [.trap]) (rest := p.afterLoop) (dst := dst)
  constructor
  · intro move
    rcases invert.mp move with ⟨_, inside, _⟩ | ⟨out, pure, eq⟩
    · exact (Nested.lime_result_stuck (r := .trap) inside).elim
    · rw [Nested.lime_label_result (r := .trap) pure] at eq
      exact eq
  · intro eq
    exact invert.mpr (.inr ⟨[.trap], .labelTrap 1 [p.loop.instr], eq⟩)

private theorem one {a b : Phase H}
    (native : Internal (p.render mem outer index arg ⟨bytes, a⟩) dst ↔
      dst = p.render mem outer index arg ⟨bytes, b⟩)
    (move : Control arg p.saved p.continuation a b)
    (unique : ∀ {endPhase}, Control arg p.saved p.continuation a endPhase → endPhase = b) :
    Internal (p.render mem outer index arg ⟨bytes, a⟩) dst ↔
      ∃ next, Control arg p.saved p.continuation a next ∧ dst = p.render mem outer index arg ⟨bytes, next⟩ := by
  rw [native]
  exact ⟨fun eq => ⟨b, move, eq⟩, fun ⟨_, edge, eq⟩ => unique edge ▸ eq⟩

theorem pending_producer {input : BitVec 64} (checked : p.Checked mem outer index) :
    CalloutAt (p.render mem outer index arg ⟨bytes, .producerInvoke input⟩)
      (p.producer.callout (p.producerContext arg) [i64 input]) :=
  ⟨rfl, checked.producer, rfl⟩

theorem internal_iff (checked : p.Checked mem outer index) (a : Phase H) (beforeContinuation : ∀ q labels, a ≠ .continuation q labels) :
    Internal (p.render mem outer index arg ⟨bytes, a⟩) dst ↔
      ∃ next, Control arg p.saved p.continuation a next ∧ dst = p.render mem outer index arg ⟨bytes, next⟩ := by
  cases a with
  | source =>
    exact one (Computed.lime_direct_call_iff (stack := [i64 arg]) (tail := []) checked.rootIndex)
      .resolve (fun edge => by cases edge; rfl)
  | invoke =>
    apply one ?_ .enter (fun edge => by cases edge; rfl)
    exact CallFrame.lime_invoke_wasm_exact (s := mem.store bytes) (caller := outer) (args := [i64 arg]) checked.root rfl
  | localGet =>
    apply one ?_ .readLocal (fun edge => by cases edge; rfl)
    apply function_iff (code := values [i64 p.saved] ++ .source (.localGet ⟨0⟩) :: .source p.loop.instr :: p.afterLoop)
    · intro out
      exact stay (saved := [i64 p.saved]) rfl (by simp) (by simp) (by simp)
    · exact Computed.lime_local_get_iff (stack := [i64 p.saved]) (i := ⟨0⟩) rfl
  | enterLoop input =>
    apply one ?_ (.openLoop input) (fun edge => by cases edge; rfl)
    apply function_iff (code := values [i64 p.saved, i64 input] ++ .source p.loop.instr :: p.afterLoop)
    · intro out
      exact stay (saved := [i64 p.saved, i64 input]) rfl (by simp [Program.loop, Loops.LimeIndexedLoop.instr])
        (by simp [Program.loop, Loops.LimeIndexedLoop.instr]) (by simp)
    · exact p.loop.entry_iff (saved := [i64 p.saved]) (args := [i64 input]) checked.loopIndex rfl
  | producerCall input =>
    apply one ?_ (.resolveProducer input) (fun edge => by cases edge; rfl)
    apply loop_iff (code := values [i64 input] ++ .source (.call p.producerIndex) :: Program.afterProducer)
    · intro out
      exact stay (saved := [i64 input]) rfl (by simp) (by simp) (by simp)
    · exact Computed.lime_direct_call_iff (stack := [i64 input]) (tail := Program.afterProducer) checked.producerIndex
  | producerInvoke input =>
    exact ⟨fun step => ((pending_producer checked (arg := arg) (bytes := bytes) (input := input)).not_internal step).elim,
      fun ⟨_, edge, _⟩ => by cases edge⟩
  | test res next condition =>
    apply one ?_ (.test res next condition) (fun edge => by cases edge; rfl)
    have lifted := loop_iff (p := p) (arg := arg) (outer := outer) (s := mem.store bytes) (dst := dst)
      (code := values [i32 res, i64 next, i32 condition] ++ Program.afterProducer)
      (next := values [i32 res, i64 next] ++ (if condition = 0 then [] else [.source (.br ⟨0⟩)]) ++ [.source .drop])
      (fun _ => stay (saved := [i32 res, i64 next, i32 condition]) rfl (by simp) (by simp) (by simp))
      (Computed.lime_br_if_iff (saved := [i32 res, i64 next]) (condition := condition) (depth := ⟨0⟩))
    by_cases zero : condition = 0
    · simpa only [ite_eq_left zero, Program.render, Program.code, List.append_nil] using lifted
    · simpa only [ite_eq_right zero, Program.render, Program.code, List.append_assoc, List.singleton_append] using lifted
  | restart scratch next =>
    apply one ?_ (.restart scratch next) (fun edge => by cases edge; rfl)
    refine function_iff (p := p) (arg := arg) (outer := outer) (s := mem.store bytes)
      (code := p.loopCode (values [i32 scratch, i64 next] ++ [.source (.br ⟨0⟩), .source .drop]))
      (next := values [i64 p.saved, i64 next] ++ .source p.loop.instr :: p.afterLoop) ?_ ?_
    · intro out
      exact stay (saved := [i64 p.saved]) rfl (by simp) (by simp) (by simp)
    · exact p.loop.restart_iff (saved := [i64 p.saved]) (scratch := [i32 scratch]) (args := [i64 next])
        checked.loopIndex rfl
  | dropInput res input =>
    apply one ?_ (.dropInput res input) (fun edge => by cases edge; rfl)
    refine loop_iff (p := p) (arg := arg) (outer := outer) (s := mem.store bytes)
      (code := values [i32 res, i64 input] ++ [.source .drop]) (next := values [i32 res]) ?_ ?_
    · intro out
      exact stay (saved := [i32 res, i64 input]) rfl (by simp) (by simp) (by simp)
    · exact Computed.lime_drop_iff (stack := [i32 res]) (v := i64 input) (rest := [])
  | loopResult res =>
    apply one ?_ (.loopResult res) (fun edge => by cases edge; rfl)
    apply function_iff (code := p.loopCode (values [i32 res]))
    · intro out
      exact stay (saved := [i64 p.saved]) rfl (by simp) (by simp) (by simp)
    · exact p.loop.result_iff (saved := [i64 p.saved]) (payload := [i32 res]) checked.loopIndex rfl
  | loopTrap tail =>
    cases tail with
    | nil =>
      apply one ?_ .exitLoop (fun edge => by
        cases edge with
        | exitLoop => rfl
        | eraseLoop split active => exact (active (List.append_eq_nil_iff.mp split.symm).1).elim)
      exact function_iff (fun _ => stay (saved := [i64 p.saved]) rfl (by simp) (by simp) (by simp))
        loop_trap_exit
    | cons instr tail =>
      have stays (out : List Admin) :
          ¬ PureStep (p.active arg).module.types [.label 1 [p.loop.instr] (.trap :: instr :: tail)] out :=
        stay (saved := []) rfl (by simp) (by simp) (by simp)
      change Internal ⟨_, _, p.functionCode arg (p.loopCode (.trap :: instr :: tail))⟩ dst ↔ _
      rw [loop_context stays]
      constructor
      · rintro ⟨mid, move, rfl⟩
        rcases (Computed.lime_trap_front_iff (stack := []) (tail := instr :: tail)).mp move with ⟨kept, removed, cut, rest, stack, split, active, rfl⟩
        obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp stack.symm
        exact ⟨.loopTrap rest, .eraseLoop split (by simpa using active), rfl⟩
      · rintro ⟨_, edge, rfl⟩
        cases edge with
        | eraseLoop split active =>
          exact ⟨_, (Computed.lime_trap_front_iff (stack := []) (tail := instr :: tail)).mpr
            ⟨[], [], _, _, rfl, split, .inr active, rfl⟩, rfl⟩
  | continuation q labels => exact (beforeContinuation q labels rfl).elim

end Silmaril.Wasm.Institution.Operational.HostCall.Lime1.IndexedLoop.Proofs
