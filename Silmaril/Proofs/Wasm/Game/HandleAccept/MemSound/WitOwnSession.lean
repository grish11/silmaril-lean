module

public import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session.Defs
import Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Nested.Thms

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnSession

open Silmaril.Formats Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own
  Silmaril.Wasm.Game.HandleAccept.MemSound.WitAst.Own.Session

private theorem commit_le (rt : RT) (indices : Nested.Reservations) :
    (rt.killAll indices.val).Le rt := by
  intro resource index rep found
  by_cases member : index ∈ indices.val
  · rw [Nested.commit_dead rt indices member resource] at found
    cases found
  · simpa only [RT.lookup, RT.killAll, member, ↓reduceIte] using found

private theorem nested_le {S : WitSig} {tagOf : BitVec 32 → Option S.Tag} {mode : NodeMode}
    {rt updated : RT} {observed : Accept.Callout} {value : Op S × List (BitVec 32)}
    (decoded : Nested.checkedNode S tagOf mode rt observed = .ok (value, updated)) :
    updated.Le rt := by
  simp only [Nested.checkedNode, bind, Except.bind, pure, Except.pure] at decoded
  split at decoded
  · cases decoded
  · rename_i args _
    split at decoded
    · cases decoded
    · rename_i raw _
      rcases raw with ⟨rawOp, children⟩
      split at decoded
      · cases decoded
      · rename_i resolved _
        rcases resolved with ⟨op, indices⟩
        cases decoded
        exact commit_le rt indices

open Silmaril.Wasm.Game.HandleAccept.MemSound in
public theorem answer_le {S : WitSig} {Q : Type} {K : Contract S Q} {memory : Option Nat}
    {before after : State Q} {call : UCall Nat} {reply : UReply}
    (answer : Answer K memory before call reply after) : after.resources.Le before.resources := by
  cases answer with
  | reject | decline | other => exact fun _ _ _ found => found
  | returnHandle _ decoded _ _ =>
    cases memory with
    | none =>
      simp only [Contract.attempt, bind, Except.bind] at decoded
      split at decoded <;> cases decoded
    | some addr =>
      simp only [Contract.attempt, checkedAt, bind, Except.bind] at decoded
      split at decoded
      · cases decoded
      · split at decoded
        · cases decoded
        · exact nested_le decoded

public theorem rejected_answer {S : WitSig} {Q : Type} {K : Contract S Q} {memory : Option Nat}
    {before after : State Q} {call : UCall Nat} {reply : UReply} {issue : NodeIssue}
    (node : call.target = K.code) (rejected : K.attempt memory before.resources call = .error issue)
    (answer : Answer K memory before call reply after) : reply = ⟨call.store, .trap⟩ ∧ after = before := by
  cases answer with
  | reject | decline => exact ⟨rfl, rfl⟩
  | returnHandle _ decoded _ _ => rw [rejected] at decoded; cases decoded
  | other different _ => exact (different node).elim

public theorem session_le {S : WitSig} {Q Entry Input Output Exit : Type} {K : Contract S Q}
    {P : Silmaril.Wasm.Numerics.Profile} {m : Silmaril.Wasm.Module} {memory : Option Nat}
    {roles : Roles Entry Input Output Exit} {init : Config Nat} {initial : State Q} {exports : List Nat}
    {phase : Phase} {pending : Bool} {current : Config Nat × (K.env memory).S} {tags}
    (history : TSession P (K.env memory) m memory roles init initial exports phase pending current tags) :
    current.2.resources.Le initial.resources := by
  induction history with
  | start => exact fun _ _ _ found => found
  | internal _ _ ih | call _ _ ih | invoke _ _ _ _ _ ih | ret _ _ ih => exact ih
  | answer _ _ answer ih =>
    exact fun resource index rep found => ih resource index rep (answer_le answer resource index rep found)

end Silmaril.Proofs.Wasm.Game.HandleAccept.MemSound.WitOwnSession
