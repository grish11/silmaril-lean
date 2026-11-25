module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Common
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Proofs.Lime1

open Execution
open Wasm.Lime1.Execution
open Execution.Runtime (Value AdminInstr)
open CallContinuation.OuterCall.Ranked
open CallContinuation.OuterCall.Computed
open CallContinuation
open CallContinuation.OuterCall
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {s : Store H} {call : Invocation} {program : Graph.Program}
  {rest : List Admin}

private theorem entered_config :
    limeEntered s call.caller call.callee call.saved call.args rest = call.limeCallee s rest call.entered := by
  rw [limeEntered, Graph.lime_body_expression]
  simp only [Invocation.limeCallee, Invocation.entered, Graph.Phase.render, Graph.Phase.renderAt,
    List.append_assoc, List.singleton_append]
  rfl

theorem prefix_exact (checked : call.Checked program) (allocated : program.LimeAllocated s)
    (tableFound : frameTable s call.caller = some call.site.table) :
    (call.limePrefix s rest).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) := by
  refine List.isChain_cons_cons.mpr ⟨fun _ => lime_step_iff checked.site allocated tableFound checked.resolved,
    List.isChain_cons_cons.mpr ⟨?_, .singleton _⟩⟩
  intro dst
  exact (lime_enter_iff allocated checked.found checked.resolved checked.typed).trans
    (by rw [entered_config])

private theorem frame_shape {phase : Graph.Phase} (live : phase.LabelOutcome) :
    ∃ n f body, phase.render Graph.limeAdmin call.target = [AdminInstr.frame n f body] := by
  cases phase <;> first | contradiction | exact ⟨_, _, _, rfl⟩

theorem frame_step_iff (checked : call.Checked program) (allocated : program.LimeAllocated s)
    {phase : Graph.Phase} {dst : Config H} (ready : Graph.Admitted program call.callee phase)
    (live : phase.LabelOutcome) :
    Step CallFrame.limeNoHost (call.limeCallee s rest phase) dst ↔
      ∃ out, program.FrameEdge call.address phase out ∧ dst = call.limeCallee s rest out := by
  obtain ⟨n, f, body, code⟩ := frame_shape (call := call) live
  have exactStep {mid} := Graph.lime_resolved_frame_step_iff (s := s) (caller := call.caller)
    (target := call.target) (b := mid) checked.graph allocated checked.found rfl ready (not_call live)
  constructor
  · intro step
    simp only [Invocation.limeCallee, code, List.append_assoc, List.singleton_append] at step
    obtain ⟨mid, move, rfl⟩ := CallContinuation.lime_frame_context_inv step
    obtain ⟨out, graphStep, rfl⟩ := exactStep.mp (by
      simpa only [Graph.limeConfig, code] using move)
    exact ⟨out, graphStep, rfl⟩
  · rintro ⟨out, move, rfl⟩
    have single := exactStep.mpr ⟨out, move, rfl⟩
    change Step CallFrame.limeNoHost ⟨s, call.caller, phase.render Graph.limeAdmin call.target⟩
      ⟨s, call.caller, out.render Graph.limeAdmin call.target⟩ at single
    change Step CallFrame.limeNoHost
      ⟨s, call.caller, values call.saved ++ phase.render Graph.limeAdmin call.target ++ rest⟩
      ⟨s, call.caller, values call.saved ++ out.render Graph.limeAdmin call.target ++ rest⟩
    simpa only [List.append_assoc] using Step.context single call.saved rest

theorem stopped (result : Nested.Result) (dst : Config H) :
    ¬ call.limeFrameStep rest (call.limeCallee s rest (.done result)) dst := by
  rintro ⟨⟨n, f, body, code⟩, _⟩
  have eq := List.append_cancel_left (List.append_cancel_right
    (by simpa only [Invocation.limeCallee, List.append_assoc, List.singleton_append] using code :
      (values call.saved ++ Graph.Phase.render Graph.limeAdmin call.target (.done result)) ++ rest =
      (values call.saved ++ [AdminInstr.frame n f body]) ++ rest))
  cases result with
  | trap => cases List.cons.inj eq |>.1
  | values xs =>
    have different : values xs ≠ [AdminInstr.frame n f body] := by
      simp only [values]
      apply map_ne_singleton
      intro v
      rcases v with ⟨t, bits⟩
      cases t <;> simp [value]
    exact different eq

private theorem frame_runs (checked : call.Checked program) (allocated : program.LimeAllocated s)
    {dst : Config H} :
    Relation.ReflTransGen (call.limeFrameStep rest) (call.limeCallee s rest call.entered) dst ↔
      ∃ out, program.FrameRuns call.address call.entered out ∧ Graph.Admitted program call.callee out ∧
        Entered out ∧ dst = call.limeCallee s rest out :=
  frame_runs_iff checked (call.limeCallee s rest) _ (fun ready live => by
    obtain ⟨n, f, body, code⟩ := frame_shape (call := call) live
    exact (and_iff_right ⟨n, f, body, by simp only [Invocation.limeCallee, code, List.append_assoc, List.singleton_append]⟩).trans
      (frame_step_iff checked allocated ready live)) stopped

private theorem trap_eq (phase : Graph.Phase) (live : Entered phase) :
    call.limeTrap s call.saved rest = call.limeCallee s rest phase ↔ phase = .done .trap := by
  constructor
  · intro eq
    have code : [AdminInstr.trap] = phase.render Graph.limeAdmin call.target :=
      List.append_cancel_left (List.append_cancel_right (by
        simpa only [Invocation.limeTrap, Invocation.limeCallee, List.append_assoc, List.singleton_append] using
          congrArg (fun cfg : Config H => cfg.code) eq))
    rcases live with live | ⟨result, rfl⟩
    · obtain ⟨n, f, body, frame⟩ := frame_shape (call := call) live
      rw [frame] at code
      cases List.cons.inj code |>.1
    · cases result with
      | trap => rfl
      | values xs =>
        have different : values xs ≠ [AdminInstr.trap] := by
          simp only [values]
          apply map_ne_singleton
          intro v
          rcases v with ⟨t, bits⟩
          cases t <;> simp [value]
        exact (different code.symm).elim
  · rintro rfl
    simp only [Invocation.limeTrap, Invocation.limeCallee, Graph.Phase.render, Graph.Phase.renderAt,
      Nested.resultCode, Graph.limeAdmin, List.append_assoc, List.singleton_append]

theorem run_iff (checked : call.Checked program) (allocated : program.LimeAllocated s)
    (tableFound : frameTable s call.caller = some call.site.table) {dst : Config H} :
    NativeRun (Step CallFrame.limeNoHost) (call.limeFrameStep rest) (call.limePrefix s rest)
      (call.limeCallee s rest call.entered) (call.limeTrap s call.saved rest) dst ↔
    call.Run program rest (call.limePrefix s rest) (call.limeCallee s rest) (call.limeTrap s) dst :=
  Proofs.run_iff (prefix_exact checked allocated tableFound) (frame_runs checked allocated)
    (trap_runs_iff _ _ (fun {saved rest b} => by
      simpa only [Invocation.limeTrap, List.map_id] using
        (Prefix.lime_discard_iff (s := s) (f := call.caller) id (stack := saved) (tail := rest) (dst := b))))
    trap_eq (tracked checked)

theorem steps_of_run {dst : Config H}
    (run : NativeRun (Step CallFrame.limeNoHost) (call.limeFrameStep rest) (call.limePrefix s rest)
      (call.limeCallee s rest call.entered) (call.limeTrap s call.saved rest) dst) :
    Steps CallFrame.limeNoHost (limeSource s call.caller call.site call.selector (call.saved ++ call.args) rest) dst :=
  native_steps (by simp) (fun step => step.2) run

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Proofs.Lime1
