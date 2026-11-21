module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Thms

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled

open Silmaril.Wasm Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Engine
  Silmaril.Wasm.Component.Runtime

variable {sig : Signature} {grow : SingleThreaded.GrowOracle}

/-- Preflight failure records a typed diagnostic, preserving both the reference store
and the accepted trees and claims. A later export may retry using the same store. -/
theorem acceptAttempt_preflight_refusal (contract : Contract sig) (memory : Option Nat)
    (state : HostState sig) (reference : CStore (core3 grow)) (args : List FlatValue)
    {issue : Core.Issue}
    (refused : contract.preflight memory state.writer (nodeCall contract reference args) = .error issue) :
    acceptAttempt contract memory state reference args =
      (reference, { state with refusals := .accept issue :: state.refusals }, [i32Flat 1, i32Flat 0]) := by
  unfold acceptAttempt
  rw [@Core.preflight_refusal sig grow contract memory ⟨reference, state.writer⟩
    (nodeCall contract reference args) issue refused]
  rfl

/-- A later load trap records an error without rolling back the preceding canonical
effects and without publishing a partial root. -/
theorem acceptAttempt_load_refusal (contract : Contract sig) (memory : Option Nat)
    (state : HostState sig) (reference updated : CStore (core3 grow)) (args : List FlatValue)
    {issue : Core.Issue}
    (refused : contract.attempt memory (⟨reference, state.writer⟩ : World grow sig)
      (nodeCall contract reference args) = (⟨updated, state.writer⟩, .error issue)) :
    acceptAttempt contract memory state reference args =
      (updated, { state with refusals := .accept issue :: state.refusals }, [i32Flat 1, i32Flat 0]) := by
  unfold acceptAttempt
  rw [refused]
  rfl

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Scheduled
