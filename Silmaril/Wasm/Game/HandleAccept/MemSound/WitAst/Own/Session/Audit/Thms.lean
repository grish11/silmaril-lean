module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Audit.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnAudit

public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Audit

open Silmaril.Formats Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.SingleThreaded

variable {S : WitSig} {Q Entry Input Output Exit : Type} {K : Contract S Q} {memory : Option Nat}
  {P : Profile} {m : Module} {roles : Roles Entry Input Output Exit} {init : Config Nat}
  {exports : List Nat} {phase : Phase} {pending : Bool}

/-- Erasing diagnostics leaves the same Core and writer run, including traps and retries. -/
theorem erase {initial : Journal Q} {current : Config Nat × (env K memory).S} {tags}
    (history : TSession P (env K memory) m memory roles init initial exports phase pending current tags) :
    TSession P (K.env memory) m memory roles init initial.host exports phase pending
      (current.1, current.2.host) tags :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnAudit.erase history

/-- Every checked Core run has a journal, not just its successful subsequence. The lifted
run has identical Core configurations, writer and table states, and role observations. -/
theorem instrument {initial : State Q} {current : Config Nat × (K.env memory).S} {tags}
    (history : TSession P (K.env memory) m memory roles init initial exports phase pending current tags)
    (initialEntries : List Event) :
    ∃ entries, TSession P (env K memory) m memory roles init ⟨initial, initialEntries⟩ exports phase pending
      (current.1, ⟨current.2, entries⟩) tags :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnAudit.instrument history initialEntries

/-- A journaled rejection reports the actual diagnostic. It preserves the reached Core
store and host state, so any earlier effects remain and no new tree is accepted. -/
theorem rejection {before after : Journal Q} {call : UCall Nat} {reply : UReply}
    {issue : NodeIssue} (answer : (env K memory).Ans before call reply after)
    (diagnosed : (observe K memory before.host call reply).outcome = .rejected issue) :
    call.target = K.code ∧ K.attempt memory before.host.resources call = .error issue ∧
      reply = ⟨call.store, .trap⟩ ∧ after.host = before.host ∧
      after.entries = ⟨call.target, call.args, .trap, .rejected issue⟩ :: before.entries :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnAudit.rejection answer diagnosed

/-- A reached preflight refusal records one diagnostic and unwinds the current call. A
subsequent well-typed export starts with the same store and all earlier host effects. -/
theorem reject_then_invoke {initial state : Journal Q} {current : Config Nat} {tags} {ctx : Ctx}
    {address code next : Nat} {args nextArgs : List Val} {issue : NodeIssue}
    (history : TSession P (env K memory) m memory roles init initial exports .run true (current, state) tags)
    (redex : decompose? current.store current.code = some (ctx, address, code, args)) (node : code = K.code)
    (rejected : K.attempt memory state.host.resources ⟨code, current.store, args⟩ = .error issue)
    (exported : next ∈ exports) (typed : InvokeOk current.store next nextArgs) :
    ∃ resumedTags, TSession P (env K memory) m memory roles init initial exports .run false
      (invoke current.store next nextArgs,
        ⟨state.host, ⟨code, args, .trap, .rejected issue⟩ :: state.entries⟩) resumedTags :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnAudit.reject_then_invoke
    history redex node rejected exported typed

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Audit
