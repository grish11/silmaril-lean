module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Audit.Defs
import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Thms
import Silmaril.Wasm.Game.IOAccept.Thms
import Silmaril.Wasm.Game.Linking.Trap.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnAudit

open Silmaril.Formats Silmaril.Wasm Silmaril.Wasm.Numerics Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Audit

variable {S : WitSig} {Q Entry Input Output Exit : Type} {K : Contract S Q} {memory : Option Nat}
  {P : Profile} {m : Module} {roles : Roles Entry Input Output Exit} {init : Config Nat}
  {exports : List Nat} {phase : Phase} {pending : Bool}

theorem erase {initial : Journal Q} {current : Config Nat × (env K memory).S} {tags}
    (history : TSession P (env K memory) m memory roles init initial exports phase pending current tags) :
    TSession P (K.env memory) m memory roles init initial.host exports phase pending
      (current.1, current.2.host) tags := by
  induction history with
  | start => exact .start
  | internal _ step ih => exact .internal ih step
  | call _ redex ih => exact .call ih redex
  | answer _ redex answer ih => exact .answer ih redex answer.1
  | invoke _ allowed finished exported typed ih => exact .invoke ih allowed finished exported typed
  | ret _ finished ih => exact .ret ih finished

theorem instrument {initial : State Q} {current : Config Nat × (K.env memory).S} {tags}
    (history : TSession P (K.env memory) m memory roles init initial exports phase pending current tags)
    (initialEntries : List Event) :
    ∃ entries, TSession P (env K memory) m memory roles init ⟨initial, initialEntries⟩ exports phase pending
      (current.1, ⟨current.2, entries⟩) tags := by
  induction history with
  | start => exact ⟨initialEntries, .start⟩
  | internal _ step ih => obtain ⟨entries, run⟩ := ih; exact ⟨entries, .internal run step⟩
  | call _ redex ih => obtain ⟨entries, run⟩ := ih; exact ⟨entries, .call run redex⟩
  | answer _ redex answer ih =>
    obtain ⟨_, run⟩ := ih
    exact ⟨_, .answer run redex ⟨answer, rfl⟩⟩
  | invoke _ allowed finished exported typed ih =>
    obtain ⟨entries, run⟩ := ih
    exact ⟨entries, .invoke run allowed finished exported typed⟩
  | ret _ finished ih => obtain ⟨entries, run⟩ := ih; exact ⟨entries, .ret run finished⟩

theorem rejection {before after : Journal Q} {call : UCall Nat} {reply : UReply}
    {issue : NodeIssue} (answer : (env K memory).Ans before call reply after)
    (diagnosed : (observe K memory before.host call reply).outcome = .rejected issue) :
    call.target = K.code ∧ K.attempt memory before.host.resources call = .error issue ∧
      reply = ⟨call.store, .trap⟩ ∧ after.host = before.host ∧
      after.entries = ⟨call.target, call.args, .trap, .rejected issue⟩ :: before.entries := by
  have target : call.target = K.code := by
    by_contra different
    simp [observe, different] at diagnosed
  have attempt : K.attempt memory before.host.resources call = .error issue := by
    simp only [observe, target, ite_true] at diagnosed
    split at diagnosed
    · rename_i actual failed
      cases diagnosed
      exact failed
    · split at diagnosed <;> cases diagnosed
  obtain ⟨rfl, preserved⟩ := rejected_answer target attempt answer.1
  exact ⟨target, attempt, rfl, preserved, by simpa [observe, target, attempt] using answer.2⟩

theorem reject_then_invoke {initial state : Journal Q} {current : Config Nat} {tags} {ctx : Ctx}
    {address code next : Nat} {args nextArgs : List Val} {issue : NodeIssue}
    (history : TSession P (env K memory) m memory roles init initial exports .run true (current, state) tags)
    (redex : decompose? current.store current.code = some (ctx, address, code, args)) (node : code = K.code)
    (rejected : K.attempt memory state.host.resources ⟨code, current.store, args⟩ = .error issue)
    (exported : next ∈ exports) (typed : InvokeOk current.store next nextArgs) :
    ∃ resumedTags, TSession P (env K memory) m memory roles init initial exports .run false
      (invoke current.store next nextArgs,
        ⟨state.host, ⟨code, args, .trap, .rejected issue⟩ :: state.entries⟩) resumedTags := by
  have logged : (env K memory).Ans state ⟨code, current.store, args⟩ ⟨current.store, .trap⟩
      ⟨state.host, ⟨code, args, .trap, .rejected issue⟩ :: state.entries⟩ := by
    refine ⟨Answer.reject node rejected, ?_⟩
    dsimp only [observe]
    rw [ite_eq_left node, rejected]
  have trapped := (TSession.answer history redex logged).of_core_steps
    (Linking.fill_trap_steps P current.store ctx current.frame)
  exact ⟨_, .invoke (c := ⟨current.store, current.frame, [.trap]⟩)
    (.ret trapped (r := .trap) rfl) (by decide) ⟨.trap, rfl⟩ exported typed⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnAudit
