module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Core

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)

theorem refusal_keeps_writer {sig : Signature} {grow : SingleThreaded.GrowOracle} {contract : Contract sig}
    {memory : Option Nat} {state updated : World grow sig} {call : UCall Nat} {issue : Core.Issue}
    (refused : attempt contract memory state call = (updated, .error issue)) :
    updated.writer = state.writer := by
  unfold attempt at refused
  split at refused
  split at refused
  · cases refused; rfl
  · cases refused

theorem success_publishes {sig : Signature} {grow : SingleThreaded.GrowOracle} {contract : Contract sig}
    {memory : Option Nat} {state updated : World grow sig} {call : UCall Nat} {handle : BitVec 32}
    (success : attempt contract memory state call = (updated, .ok handle)) :
    ∃ tree, updated.writer.accepted = tree :: state.writer.accepted ∧
      updated.writer.held = rootReceipts tree ++ state.writer.held ∧
      updated.writer.endpoints = rootEndpoints tree ++ state.writer.endpoints ∧
      handle = BitVec.ofNat 32 (state.writer.accepted.length + 1) := by
  cases loaded : load contract memory state call with
  | mk reference result =>
    cases result with
    | error issue => simp [attempt, loaded, Except.bind] at success
    | ok tree =>
      cases registered : state.writer.register tree with
      | error issue => simp [attempt, loaded, registered, Except.bind, Except.mapError] at success
      | ok writer =>
        simp only [attempt, loaded, registered, Except.bind, Except.mapError] at success
        cases success
        obtain ⟨history, owners, endpoints⟩ := register_claims registered
        exact ⟨tree, history, owners, endpoints, by rw [history]; rfl⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Core
