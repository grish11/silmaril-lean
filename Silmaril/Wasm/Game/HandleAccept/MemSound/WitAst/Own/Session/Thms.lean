module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Defs
import Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnSession
import Silmaril.Wasm.Game.IOAccept.Thms
import Silmaril.Wasm.Game.Linking.Trap.Thms

@[expose] public section

namespace Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session

open Silmaril.Formats Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.Accept

variable {S : WitSig} {Q : Type} {K : Contract S Q} {memory : Option Nat}

/-- A rejected node preserves the current Core store and the entire host state. -/
theorem rejected_answer {before after : State Q} {call : UCall Nat} {reply : UReply}
    {issue : NodeIssue} (node : call.target = K.code)
    (rejected : K.attempt memory before.resources call = .error issue)
    (answer : Answer K memory before call reply after) :
    reply = ⟨call.store, .trap⟩ ∧ after = before :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnSession.rejected_answer node rejected answer

/-- A typed failure has exactly one answer. No writer transition is taken: any accumulated
acceptances in the writer state persist, and the rejected call adds none. -/
theorem rejected_answer_iff {before after : State Q} {call : UCall Nat} {reply : UReply}
    {issue : NodeIssue} (node : call.target = K.code)
    (rejected : K.attempt memory before.resources call = .error issue) :
    Answer K memory before call reply after ↔ reply = ⟨call.store, .trap⟩ ∧ after = before :=
  ⟨rejected_answer node rejected, fun ⟨hr, hs⟩ => by rw [hr, hs]; exact .reject node rejected⟩

/-- Over any allowed sequence of invocations, a move-only checked host cannot recreate a
consumed resource or change the type or representation of a surviving slot. -/
theorem session_le {Entry Input Output Exit : Type} {P : Silmaril.Wasm.Numerics.Profile}
    {m : Silmaril.Wasm.Module} {roles : Roles Entry Input Output Exit} {init : Config Nat}
    {initial : State Q} {exports : List Nat} {phase : Phase} {pending : Bool}
    {current : Config Nat × (K.env memory).S} {tags}
    (history : TSession P (K.env memory) m memory roles init initial exports phase pending current tags) :
    current.2.resources.Le initial.resources :=
  Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnSession.session_le history

/-- Preflight failure extends a real traced session by a trap answer. The trap is plugged
into the existing Core context using the store at the call, not the instantiation store. -/
theorem reject_extends_session {Entry Input Output Exit : Type} {P : Silmaril.Wasm.Numerics.Profile}
    {m : Silmaril.Wasm.Module} {roles : Roles Entry Input Output Exit} {init c : Config Nat}
    {initial state : State Q} {exports : List Nat} {phase : Phase} {tags} {ctx : Ctx}
    {address code : Nat} {args : List Val} {issue : NodeIssue}
    (history : TSession P (K.env memory) m memory roles init initial exports phase true (c, state) tags)
    (redex : decompose? c.store c.code = some (ctx, address, code, args)) (node : code = K.code)
    (rejected : K.attempt memory state.resources ⟨code, c.store, args⟩ = .error issue) :
    TSession P (K.env memory) m memory roles init initial exports phase false
      (⟨c.store, c.frame, ctx.fill Result.trap.toAdmin⟩, state)
      (tags ++ (calloutAt? m memory c).elim [] fun observed =>
        roles.answerTags observed ⟨.trap, memOf memory c.store⟩) :=
  .answer history redex (Answer.reject node rejected)

/-- A rejected import during an export unwinds, and a subsequent well-typed invocation
can start from the same Core store, resource table and writer state. -/
theorem reject_then_invoke {Entry Input Output Exit : Type} {P : Silmaril.Wasm.Numerics.Profile}
    {m : Silmaril.Wasm.Module} {roles : Roles Entry Input Output Exit} {init c : Config Nat}
    {initial state : State Q} {exports : List Nat} {tags} {ctx : Ctx}
    {address code next : Nat} {args nextArgs : List Val} {issue : NodeIssue}
    (history : TSession P (K.env memory) m memory roles init initial exports .run true (c, state) tags)
    (redex : decompose? c.store c.code = some (ctx, address, code, args)) (node : code = K.code)
    (rejected : K.attempt memory state.resources ⟨code, c.store, args⟩ = .error issue)
    (exported : next ∈ exports) (typed : InvokeOk c.store next nextArgs) :
    ∃ resumedTags, TSession P (K.env memory) m memory roles init initial exports .run false
      (invoke c.store next nextArgs, state) resumedTags := by
  have trapped := (reject_extends_session history redex node rejected).of_core_steps
    (Linking.fill_trap_steps P c.store ctx c.frame)
  exact ⟨_, .invoke (c := ⟨c.store, c.frame, [.trap]⟩)
    (.ret trapped (r := .trap) rfl) (by decide) ⟨.trap, rfl⟩ exported typed⟩

end Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session
