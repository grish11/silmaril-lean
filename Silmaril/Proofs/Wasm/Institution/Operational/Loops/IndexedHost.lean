module

public import Silmaril.Wasm.Institution.Operational.Loops.Indexed.Defs
import Silmaril.Wasm.Institution.Operational.Blocks.Context.Thms
import Silmaril.Wasm.Institution.Operational.BranchExit.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Nested.Native.Thms
import Silmaril.Wasm.Lime1.Execution.Callout.Properties

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.Loops.LimeIndexedLoop.Proofs

open Execution.Runtime (Frame Value)
open Wasm.Lime1.Execution
open CallContinuation

variable {H : Type} {host : HostSemantics H} {s : Store H} {f : Frame}
  {loop : LimeIndexedLoop} {saved : List Value} {rest : List Admin} {dst : Config H}

private theorem withoutCallout {a b : Config H} (empty : decompose? a = none) :
    Step host a b ↔ Step CallFrame.limeNoHost a b := by
  have absent : ∀ call, ¬ CalloutAt a call := by
    intro call atCall
    have found := exists_callout_iff.mp ⟨call, atCall⟩
    simp [empty] at found
  exact (Step.internal_iff_of_not_callout absent).trans (Step.internal_iff_of_not_callout absent).symm

theorem entry_iff {args : List Value} (resolved : loop.Resolved f) (typed : loop.Parameters args) :
    Step host ⟨s, f, values (saved ++ args) ++ .source loop.instr :: rest⟩ dst ↔
      dst = ⟨s, f, values saved ++ .label loop.signature.params.length [loop.instr]
        (values args ++ expression loop.body) :: rest⟩ := by
  have lookup : blockType? f.module.types (.typeIdx loop.index) = some loop.signature := resolved
  have arity : args.length = loop.signature.params.length := by
    simpa using congrArg List.length typed
  rw [withoutCallout (by simp [decompose?, instr, asValue?]), instr, OuterCall.Computed.lime_loop_step_iff]
  constructor
  · rintro ⟨outerOperands, actual, found, split, resolution, count, eq⟩
    rw [lookup] at resolution
    cases resolution
    have prefixCount : saved.length = outerOperands.length := by
      have total := congrArg List.length split
      simp only [List.length_append] at total
      omega
    obtain ⟨rfl, rfl⟩ := List.append_inj split prefixCount
    exact eq
  · rintro rfl
    exact ⟨saved, args, loop.signature, rfl, lookup, arity, rfl⟩

theorem bad_index {stack : List Value} (missing : f.module.types[loop.index.toNat]? = none) :
    ¬ Step host ⟨s, f, values stack ++ .source loop.instr :: rest⟩ dst := by
  rw [withoutCallout (by simp [decompose?, instr, asValue?]), instr, OuterCall.Computed.lime_loop_step_iff]
  rintro ⟨_, _, _, _, found, _, _⟩
  simp [blockType?, missing] at found

theorem restart_iff {scratch args : List Value} {skipped : List Admin}
    (_resolved : loop.Resolved f) (typed : loop.Parameters args) :
    Step host ⟨s, f, values saved ++ .label loop.signature.params.length [loop.instr]
      (values (scratch ++ args) ++ .source (.br ⟨0⟩) :: skipped) :: rest⟩ dst ↔
      dst = ⟨s, f, values (saved ++ args) ++ .source loop.instr :: rest⟩ := by
  have arity : args.length = loop.signature.params.length := by
    simpa using congrArg List.length typed
  rw [withoutCallout (by simp [decompose?, asValue?]), Blocks.Context.lime_label_cont_iff]
  constructor
  · rintro (⟨_, inside, _⟩ | ⟨out, pure, rfl⟩)
    · exact (BranchExit.lime_br_vals_stuck inside).elim
    · have slice := (BranchExit.lime_label_br_cont_iff (s := s) (f := f) (host := CallFrame.limeNoHost)).mp
        (.pure s f pure)
      rcases slice with ⟨outerOperands, actual, split, count, _, eq⟩ | ⟨positive, _⟩
      · have prefixCount : scratch.length = outerOperands.length := by
          have total := congrArg List.length split
          simp only [List.length_append] at total
          omega
        obtain ⟨_, rfl⟩ := List.append_inj split prefixCount
        obtain rfl := congrArg (fun cfg : Config H => cfg.code) eq
        simp [values_append, expression, List.append_assoc]
      · exact (Nat.lt_irrefl 0 positive).elim
  · rintro rfl
    refine .inr ⟨values args ++ expression [loop.instr], ?_, ?_⟩
    · simpa only [values_append, List.append_assoc, List.singleton_append] using
        (PureStep.labelBranch (types := f.module.types) loop.signature.params.length [loop.instr] scratch args skipped arity)
    · simp [values_append, expression, List.append_assoc]

theorem result_iff {payload : List Value} (_resolved : loop.Resolved f) (_typed : loop.Results payload) :
    Step host ⟨s, f, values saved ++ .label loop.signature.params.length [loop.instr] (values payload) :: rest⟩ dst ↔
      dst = ⟨s, f, values (saved ++ payload) ++ rest⟩ := by
  rw [withoutCallout (by simp [decompose?]), Blocks.Context.lime_label_cont_iff]
  constructor
  · rintro (⟨_, inside, _⟩ | ⟨out, pure, rfl⟩)
    · exact (Nested.lime_result_stuck (r := .values payload) inside).elim
    · have exactResult := Nested.lime_label_result (r := .values payload) pure
      simp [Nested.resultCode, exactResult, values_append]
  · rintro rfl
    exact .inr ⟨values payload, .labelDone _ _ _, by simp [values_append]⟩

end Silmaril.Wasm.Institution.Operational.Loops.LimeIndexedLoop.Proofs
