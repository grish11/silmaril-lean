module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Thms
public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Trace

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims (State)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace

variable {sig : Signature} {grow : SingleThreaded.GrowOracle} {contract : Contract sig}
  {memory : Option Nat}

private theorem attempt_target {prior next : World grow sig} {call : UCall Nat} {handle : BitVec 32}
    (success : attempt contract memory prior call = (next, .ok handle)) : call.target = contract.code := by
  by_contra mismatch
  have rejects : preflight contract memory prior call = .error (.boundary (.unexpectedImport call.target)) := by
    simp only [preflight, bne_iff_ne]
    rw [ite_eq_left mismatch]
    rfl
  rw [preflight_refusal rejects] at success
  cases success

theorem history_of_session {state : World grow sig} {profile : Numerics.Profile} {module_ : Module}
    {start : Config Nat} {addrs : List Nat} {phase : Phase} {pending : Bool}
    {current : Config Nat × World grow sig} {tags : List CommitTag}
    (linked : module_.imports[contract.code]?.isSome = true)
    (session : TSession profile (env contract grow memory) module_ memory roles start state addrs
      phase pending current tags) : RootHistory state.writer.accepted current.2.writer.accepted tags := by
  refine rootHistory_of_session (fun (world : World grow sig) => world.writer.accepted) ?_ session
  intro prior call reply next answerStep
  change answer contract memory prior call reply next at answerStep
  cases ran : attempt contract memory prior call with
  | mk updated outcome =>
    simp only [answer, ran] at answerStep
    obtain ⟨rfl, rfl⟩ := answerStep
    cases outcome with
    | error issue => exact .inl ⟨congrArg State.accepted (refusal_keeps_writer ran), rfl⟩
    | ok handle =>
      have target := attempt_target ran
      obtain ⟨root, added, _, _, sameHandle⟩ := success_publishes ran
      exact .inr ⟨root, added, by simpa [target] using linked, by simp [sameHandle]⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Trace
