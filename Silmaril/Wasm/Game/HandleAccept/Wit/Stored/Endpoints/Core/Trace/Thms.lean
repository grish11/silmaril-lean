module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace.Session

public section

namespace Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept

theorem rootHistory_of_session {Root : Type} {env : SEnv UImp} (roots : env.S → List Root)
    {profile : Numerics.Profile} {module_ : Module} {memory : Option Nat} {state : env.S}
    {start : Config Nat} {addrs : List Nat} {phase : Phase} {pending : Bool}
    {current : Config Nat × env.S} {tags : List CommitTag}
    (effect : ∀ prior call reply next, env.Ans prior call reply next →
      Publishes module_ call.target reply (roots prior) (roots next))
    (session : TSession profile env module_ memory roles start state addrs phase pending current tags) :
    RootHistory (roots state) (roots current.2) tags :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace.rootHistory_of_session roots effect session

/-- Across arbitrary permitted export sequences and finite prefixes, the observed
successful replies are exactly the handles of the newly published trees, in order.
The theorem includes instantiation calls and sessions that continue after a trap. -/
theorem history_of_session {sig : Signature} {grow : SingleThreaded.GrowOracle} {contract : Contract sig}
    {memory : Option Nat} {state : World grow sig} {profile : Numerics.Profile} {module_ : Module}
    {start : Config Nat} {addrs : List Nat} {phase : Phase} {pending : Bool}
    {current : Config Nat × World grow sig} {tags : List CommitTag}
    (linked : module_.imports[contract.code]?.isSome = true)
    (session : TSession profile (contract.env grow memory) module_ memory roles start state addrs
      phase pending current tags) : History state.writer current.2.writer tags :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace.history_of_session linked session

theorem History.count {sig : Signature} {initial current : Endpoints.State sig} {tags : List CommitTag}
    (history : History initial current tags) :
    (commits tags).length + initial.accepted.length = current.accepted.length := by
  obtain ⟨added, accepted, committed⟩ := history
  simp [accepted, committed, handles]

end Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace
