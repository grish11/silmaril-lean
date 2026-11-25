module

public import Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context.Defs
public import Silmaril.Wasm.Institution.Operational.CallContinuation.OuterCall.Ranked.Graph.Native.Thms
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Core
import Silmaril.Proofs.Wasm.Institution.Operational.CallResolution.Indirect.Context.Lime1

@[expose] public section

namespace Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context

open Execution
open CallContinuation.OuterCall.Ranked
open CallContinuation
open Wasm.SingleThreaded.Det (noHost)

theorem entered_admitted {call : Invocation} {program : Graph.Program}
    (checked : call.Checked program) : Graph.Admitted program call.callee call.entered :=
  Proofs.entered_admitted checked

section Core

variable {H : Type} {P : Numerics.Profile} {s : Core.Store H}
  {call : Invocation} {program : Graph.Program} {rest : List Core.Admin}

/-- Core takes four steps through lowering, the table load, the nullable cast,
and entry by `call_ref`. Each step has an exact native successor. -/
theorem core_prefix_exact (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {addr : Nat} (tableFound : s.table? call.caller.toCore tableIndex = some (addr, call.site.table.toCore)) :
    (call.corePrefix s rest).IsChain (fun a b => ∀ dst, Core.Step P noHost a dst ↔ dst = b) :=
  Proofs.Core.prefix_exact checked allocated tableFound

theorem core_frame_step_iff (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {phase : Graph.Phase} {dst : Core.Config H} (ready : Graph.Admitted program call.callee phase)
    (live : phase.LabelOutcome) :
    Core.Step P noHost (call.coreCallee s rest phase) dst ↔
      ∃ out, program.FrameEdge call.address phase out ∧ dst = call.coreCallee s rest out :=
  Proofs.Core.frame_step_iff checked allocated ready live

/-- Read back every finite endpoint through the handoff to the caller, including
intermediate recursive activations and each native trap discard. -/
theorem core_run_iff (checked : call.Checked program) (allocated : program.CoreAllocated s)
    {addr : Nat}
    (tableFound : s.table? call.caller.toCore tableIndex = some (addr, call.site.table.toCore)) {dst : Core.Config H} :
    call.CoreRun P s rest dst ↔
      call.Run program rest (call.corePrefix s rest) (call.coreCallee s rest) (call.coreTrap s) dst :=
  Proofs.Core.run_iff checked allocated tableFound

theorem core_steps_of_run {dst : Core.Config H} (run : call.CoreRun P s rest dst) :
    Core.Steps P noHost
      (coreConfig s call.caller call.site call.selector (call.saved ++ call.args) rest .start) dst :=
  Proofs.Core.steps_of_run run

theorem core_handoff_stops (result : Nested.Result) (dst : Core.Config H) :
    ¬ call.coreFrameStep P rest (call.coreCallee s rest (.done result)) dst :=
  Proofs.Core.stopped result dst

end Core

section Lime1

open Wasm.Lime1.Execution

variable {H : Type} {s : Store H} {call : Invocation}
  {program : Graph.Program} {rest : List Admin}

/-- Lime1 resolves in one step and enters the callee in the next step. -/
theorem lime_prefix_exact (checked : call.Checked program) (allocated : program.LimeAllocated s)
    (tableFound : frameTable s call.caller = some call.site.table) :
    (call.limePrefix s rest).IsChain (fun a b => ∀ dst, Step CallFrame.limeNoHost a dst ↔ dst = b) :=
  Proofs.Lime1.prefix_exact checked allocated tableFound

theorem lime_frame_step_iff (checked : call.Checked program) (allocated : program.LimeAllocated s)
    {phase : Graph.Phase} {dst : Config H} (ready : Graph.Admitted program call.callee phase)
    (live : phase.LabelOutcome) :
    Step CallFrame.limeNoHost (call.limeCallee s rest phase) dst ↔
      ∃ out, program.FrameEdge call.address phase out ∧ dst = call.limeCallee s rest out :=
  Proofs.Lime1.frame_step_iff checked allocated ready live

theorem lime_run_iff (checked : call.Checked program) (allocated : program.LimeAllocated s)
    (tableFound : frameTable s call.caller = some call.site.table) {dst : Config H} :
    call.LimeRun s rest dst ↔
      call.Run program rest (call.limePrefix s rest) (call.limeCallee s rest) (call.limeTrap s) dst :=
  Proofs.Lime1.run_iff checked allocated tableFound

theorem lime_steps_of_run {dst : Config H} (run : call.LimeRun s rest dst) :
    Steps CallFrame.limeNoHost
      (limeSource s call.caller call.site call.selector (call.saved ++ call.args) rest) dst :=
  Proofs.Lime1.steps_of_run run

theorem lime_handoff_stops (result : Nested.Result) (dst : Config H) :
    ¬ call.limeFrameStep rest (call.limeCallee s rest (.done result)) dst :=
  Proofs.Lime1.stopped result dst

end Lime1

end Silmaril.Wasm.Institution.Operational.CallResolution.Indirect.Context
