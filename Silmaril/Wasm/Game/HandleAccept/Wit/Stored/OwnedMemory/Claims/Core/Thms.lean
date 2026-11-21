module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Core

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Canon
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)

variable {sig : Signature} {grow : SingleThreaded.GrowOracle} {contract : Contract sig}
  {memory : Option Nat} {state : World grow sig} {call : UCall Nat}

theorem preflight_refusal {issue : Issue} (refused : preflight contract memory state call = .error issue) :
    attempt contract memory state call = (state, .error issue) := by
  simp [attempt, load, refused, Except.bind]

theorem FlatSource.preflight_refusal (source : FlatSource sig) {args : List FlatValue} {issue : Issue}
    (refused : source.preflight state args = .error issue) :
    source.load state args = (state.reference, .error issue) := by
  simp [FlatSource.load, refused]

theorem refusal_traps {issue : Issue} {updated : World grow sig}
    (refused : attempt contract memory state call = (updated, .error issue)) :
    answer contract memory state call ⟨call.store, .trap⟩ updated := by
  simp [answer, refused]

theorem refusal_keeps_writer {issue : Issue} {updated : World grow sig}
    (refused : attempt contract memory state call = (updated, .error issue)) :
    updated.writer = state.writer :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Core.refusal_keeps_writer refused

/-- A successful call publishes exactly one root and the claims of that root only. -/
theorem success_publishes {handle : BitVec 32} {updated : World grow sig}
    (success : attempt contract memory state call = (updated, .ok handle)) :
    ∃ tree, updated.writer.accepted = tree :: state.writer.accepted ∧
      updated.writer.held = rootReceipts tree ++ state.writer.held ∧
      updated.writer.endpoints = rootEndpoints tree ++ state.writer.endpoints ∧
      handle = BitVec.ofNat 32 (state.writer.accepted.length + 1) :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Core.success_publishes success

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
