module

public import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Common
import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Computed.Prefix.Native.Thms
import Silmaril.Wasm.Institution.Operational.CallContinuation.Native.Thms
import Silmaril.Wasm.Execution.Core.Inversion.Thms
import Silmaril.Wasm.Execution.Core.Sim.Context

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Proofs.Core

open Execution
open Execution.Core
open Execution.Runtime (Value)
open CallContinuation.OuterCall.Ranked
open CallContinuation.OuterCall.Computed
open CallContinuation
open CallContinuation.OuterCall
open Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Numerics.Profile} {s : Store H} {call : Invocation} {program : Graph.Program}
  {rest : List Admin}

private theorem entered_config :
    coreEntered s call.caller call.callee call.saved call.args rest = call.coreCallee s rest call.entered := by
  rw [coreEntered, Graph.core_body_expression]
  simp only [Invocation.coreCallee, Invocation.entered, Graph.Phase.render, Graph.Phase.renderAt,
    List.append_assoc, List.singleton_append]
  rfl

theorem prefix_exact (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {addr : Nat} (tableFound : s.table? call.caller.toCore tableIndex = some (addr, call.site.table.toCore)) :
    (call.corePrefix s rest).IsChain (fun a b => ∀ dst, Step P noHost a dst ↔ dst = b) := by
  have exactSteps := core_trace_exact (P := P) (stack := call.saved ++ call.args)
    (rest := rest) checked.site allocated tableFound checked.resolved
  obtain ⟨first, exactSteps⟩ := List.isChain_cons_cons.mp exactSteps
  obtain ⟨lookup, exactSteps⟩ := List.isChain_cons_cons.mp exactSteps
  obtain ⟨cast, _⟩ := List.isChain_cons_cons.mp exactSteps
  refine List.isChain_cons_cons.mpr ⟨first, List.isChain_cons_cons.mpr
    ⟨lookup, List.isChain_cons_cons.mpr ⟨cast, List.isChain_cons_cons.mpr ⟨?_, .singleton _⟩⟩⟩⟩
  intro dst
  exact (core_enter_iff allocated checked.found checked.resolved checked.typed).trans
    (by rw [entered_config])

private theorem frame_shape {phase : Graph.Phase} (live : phase.LabelOutcome) :
    ∃ n f body, phase.render Graph.coreAdmin call.target = [Admin.frame n f body] := by
  cases phase <;> first | contradiction | exact ⟨_, _, _, rfl⟩

theorem frame_step_iff (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {phase : Graph.Phase} {dst : Config H} (ready : Graph.Admitted program call.callee phase)
    (live : phase.LabelOutcome) :
    Step P noHost (call.coreCallee s rest phase) dst ↔
      ∃ out, program.FrameEdge call.address phase out ∧ dst = call.coreCallee s rest out := by
  obtain ⟨n, f, body, code⟩ := frame_shape (call := call) live
  have exactStep {mid} := Graph.core_resolved_frame_step_iff (P := P) (s := s) (caller := call.caller)
    (target := call.target) (b := mid) checked.graph allocated checked.found rfl ready (not_call live)
  constructor
  · intro step
    simp only [Invocation.coreCallee, code, List.append_assoc, List.singleton_append] at step
    obtain ⟨mid, move, rfl⟩ := Step.ctx_in_seq (X := .frame n f body) (by simp [Admin.IsCtx]) step
    obtain ⟨out, graphStep, rfl⟩ := exactStep.mp (by
      simpa only [Graph.coreConfig, code] using move)
    exact ⟨out, graphStep, rfl⟩
  · rintro ⟨out, move, rfl⟩
    have single := exactStep.mpr ⟨out, move, rfl⟩
    change Step P noHost ⟨s, call.caller.toCore, phase.render Graph.coreAdmin call.target⟩
      ⟨s, call.caller.toCore, out.render Graph.coreAdmin call.target⟩ at single
    change Step P noHost
      ⟨s, call.caller.toCore, Core.vals (call.saved.map Value.toCore) ++ phase.render Graph.coreAdmin call.target ++ rest⟩
      ⟨s, call.caller.toCore, Core.vals (call.saved.map Value.toCore) ++ out.render Graph.coreAdmin call.target ++ rest⟩
    exact by
      simpa only [List.append_assoc, List.singleton_append] using
        Core.Sim.Step.vals_left (Core.Sim.Step.append_right single rest) (call.saved.map Value.toCore)

theorem stopped (result : Nested.Result) (dst : Config H) :
    ¬ call.coreFrameStep P rest (call.coreCallee s rest (.done result)) dst := by
  rintro ⟨⟨n, f, body, code⟩, _⟩
  have eq := List.append_cancel_left (List.append_cancel_right
    (by simpa only [Invocation.coreCallee, List.append_assoc, List.singleton_append] using code :
      (Core.vals (call.saved.map Value.toCore) ++ Graph.Phase.render Graph.coreAdmin call.target (.done result)) ++ rest =
      (Core.vals (call.saved.map Value.toCore) ++ [Admin.frame n f body]) ++ rest))
  cases result with
  | trap => cases List.cons.inj eq |>.1
  | values xs =>
    have different : coreValues xs ≠ [Admin.frame n f body] := by
      simp only [coreValues, Core.vals, List.map_map, Function.comp_def]
      apply map_ne_singleton
      intro v eq
      have h := congrArg Core.Admin.val? eq
      simp only [Core.Admin.val?_toAdmin] at h
      cases h
    exact different eq

private theorem frame_runs (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {dst : Config H} :
    Relation.ReflTransGen (call.coreFrameStep P rest) (call.coreCallee s rest call.entered) dst ↔
      ∃ out, program.FrameRuns call.address call.entered out ∧ Graph.Admitted program call.callee out ∧
        Entered out ∧ dst = call.coreCallee s rest out :=
  frame_runs_iff checked (call.coreCallee s rest) _ (fun ready live => by
    obtain ⟨n, f, body, code⟩ := frame_shape (call := call) live
    exact (and_iff_right ⟨n, f, body, by simp only [Invocation.coreCallee, code, List.append_assoc, List.singleton_append]⟩).trans
      (frame_step_iff (P := P) checked allocated ready live)) stopped

private theorem trap_eq (phase : Graph.Phase) (live : Entered phase) :
    call.coreTrap s call.saved rest = call.coreCallee s rest phase ↔ phase = .done .trap := by
  constructor
  · intro eq
    have code : [Admin.trap] = phase.render Graph.coreAdmin call.target :=
      List.append_cancel_left (List.append_cancel_right (by
        simpa only [Invocation.coreTrap, Invocation.coreCallee, List.append_assoc, List.singleton_append] using
          congrArg (fun cfg : Config H => cfg.code) eq))
    rcases live with live | ⟨result, rfl⟩
    · obtain ⟨n, f, body, frame⟩ := frame_shape (call := call) live
      rw [frame] at code
      cases List.cons.inj code |>.1
    · cases result with
      | trap => rfl
      | values xs =>
        have different : coreValues xs ≠ [Admin.trap] := by
          simp only [coreValues, Core.vals, List.map_map, Function.comp_def]
          apply map_ne_singleton
          intro v eq
          have h := congrArg Core.Admin.val? eq
          simp only [Core.Admin.val?_toAdmin] at h
          cases h
        exact (different code.symm).elim
  · rintro rfl
    simp only [Invocation.coreTrap, Invocation.coreCallee, Graph.Phase.render, Graph.Phase.renderAt,
      Nested.resultCode, Graph.coreAdmin, List.append_assoc, List.singleton_append]

theorem run_iff (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {addr : Nat}
    (tableFound : s.table? call.caller.toCore tableIndex = some (addr, call.site.table.toCore)) {dst : Config H} :
    NativeRun (Step P noHost) (call.coreFrameStep P rest) (call.corePrefix s rest)
      (call.coreCallee s rest call.entered) (call.coreTrap s call.saved rest) dst ↔
    call.Run program rest (call.corePrefix s rest) (call.coreCallee s rest) (call.coreTrap s) dst :=
  Proofs.run_iff (prefix_exact (P := P) checked allocated tableFound) (frame_runs (P := P) checked allocated)
    (trap_runs_iff _ _ (fun {saved rest b} => by
      simpa only [Invocation.coreTrap, List.map_id] using
        (Prefix.core_discard_iff (P := P) (s := s) (f := call.caller) id (stack := saved) (tail := rest) (dst := b))))
    trap_eq (tracked checked)

theorem steps_of_run {dst : Config H}
    (run : NativeRun (Step P noHost) (call.coreFrameStep P rest) (call.corePrefix s rest)
      (call.coreCallee s rest call.entered) (call.coreTrap s call.saved rest) dst) :
    Steps P noHost (coreConfig s call.caller call.site call.selector (call.saved ++ call.args) rest .start) dst :=
  native_steps (by simp) (fun step => step.2) run

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Proofs.Core
