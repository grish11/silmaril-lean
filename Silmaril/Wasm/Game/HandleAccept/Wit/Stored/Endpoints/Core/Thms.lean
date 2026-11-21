module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Defs
public import Silmaril.Wasm.Component.Reference.Machine.Step.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Run

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon
  Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime

variable {sig : Signature} {grow : SingleThreaded.GrowOracle} {contract : Contract sig}
  {memory : Option Nat} {state : World grow sig} {call : UCall Nat}

theorem preflight_refusal {issue : Issue}
    (refused : contract.preflight memory state.writer call = .error issue) :
    contract.attempt memory state call = (state, .error issue) := by
  simp [Contract.attempt, Contract.load, refused, Except.bind]

theorem preflight_refusal_answers_trap {issue : Issue}
    (refused : contract.preflight memory state.writer call = .error issue) :
    contract.answer memory state call ⟨call.store, .trap⟩ state := by
  simp [Contract.answer, preflight_refusal refused]

theorem refusal_answers_trap {issue : Issue} {updated : World grow sig}
    (refused : contract.attempt memory state call = (updated, .error issue)) :
    contract.answer memory state call ⟨call.store, .trap⟩ updated := by
  simp [Contract.answer, refused]

theorem refusal_keeps_writer {issue : Issue} {updated : World grow sig}
    (refused : contract.attempt memory state call = (updated, .error issue)) :
    updated.writer = state.writer := by
  unfold Contract.attempt at refused
  split at refused
  split at refused
  · cases refused; rfl
  · cases refused

/-- Success of the call-local interpreter has precisely the reference store effects
of evaluating the read/update prefix, up to the caller's result continuation. -/
theorem runLocal_steps {E : CoreEngine} {Value : Type} (program : P E Unit Value)
    (store updated : CStore E) (value : Value) (finish : Value → P E Unit (Ret E))
    (ready : HostReady Unit) (dispatch : Call E → P E Unit (Ret E))
    (success : runLocal program store = (updated, .ok value)) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps .deterministic ready dispatch
        { store, host := (), ctl := [.ofProg none (program >>= finish)] } labels
        { store := updated, host := (), ctl := [.ofProg none (finish value)] } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.runLocal_steps
    program store updated value finish ready dispatch success

/-- On a canonical trap, the call-local interpreter retains the store at the trap.
The complete reference machine additionally locks it down; the Core contract instead
traps only the enclosing Core call and does not roll back the preceding updates. -/
theorem runLocal_trap_steps {E : CoreEngine} {Value : Type} (program : P E Unit Value)
    (store updated : CStore E) (reason : TrapReason) (finish : Value → P E Unit (Ret E))
    (ready : HostReady Unit) (dispatch : Call E → P E Unit (Ret E))
    (failure : runLocal program store = (updated, .error (.trapped reason))) :
    ∃ labels, labels.all (· matches .tau) = true ∧
      Machine.Steps .deterministic ready dispatch
        { store, host := (), ctl := [.ofProg none (program >>= finish)] } (labels ++ [.trap reason])
        { store := Machine.StepDefs.lockdownSt updated, host := (), ctl := [] } :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.runLocal_trap_steps
    program store updated reason finish ready dispatch failure

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core
