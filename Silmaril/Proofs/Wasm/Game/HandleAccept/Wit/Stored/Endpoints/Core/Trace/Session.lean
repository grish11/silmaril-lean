module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core
  Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace

variable {sig : Signature} {grow : SingleThreaded.GrowOracle} {contract : Contract sig}
  {memory : Option Nat} {state updated : World grow sig} {call : UCall Nat}

theorem attempt_publishes {handle : BitVec 32}
    (success : contract.attempt memory state call = (updated, .ok handle)) :
    ∃ tree, updated.writer.accepted = tree :: state.writer.accepted ∧
      handle = BitVec.ofNat 32 (state.writer.accepted.length + 1) ∧ call.target = contract.code := by
  have target : call.target = contract.code := by
    by_contra mismatch
    have rejected : contract.preflight memory state.writer call = .error (.unexpectedImport call.target) := by
      simp only [Contract.preflight, bne_iff_ne]
      rw [ite_eq_left mismatch]
      rfl
    rw [preflight_refusal rejected] at success
    cases success
  cases loaded : contract.load memory state call with
  | mk reference result =>
    cases result with
    | error reason => simp [Contract.attempt, loaded, Except.bind] at success
    | ok tree =>
      cases registered : state.writer.register tree with
      | error reason => simp [Contract.attempt, loaded, registered, Except.bind, Except.mapError] at success
      | ok writer =>
        simp only [Contract.attempt, loaded, Except.bind, registered, Except.mapError] at success
        cases success
        simp only [Endpoints.State.register] at registered
        split at registered <;> cases registered
        exact ⟨tree, rfl, rfl, target⟩

private theorem commits_append (prior extra : List CommitTag) :
    commits (prior ++ extra) = commits prior ++ commits extra := List.filterMap_append

private theorem append_quiet {Root : Type} {first last : List Root} {prior extra : List CommitTag}
    (history : RootHistory first last prior) (quiet : commits extra = []) :
    RootHistory first last (prior ++ extra) := by
  obtain ⟨added, accepted, committed⟩ := history
  exact ⟨added, accepted, by simpa [commits_append, quiet] using committed⟩

private theorem append_root {Root : Type} {first last next : List Root} {prior extra : List CommitTag}
    {root : Root} (history : RootHistory first last prior)
    (accepted : next = root :: last)
    (committed : commits extra = [BitVec.ofNat 32 (last.length + 1)]) :
    RootHistory first next (prior ++ extra) := by
  obtain ⟨added, previous, tagged⟩ := history
  refine ⟨added ++ [root], by simp [accepted, previous, List.reverse_append], ?_⟩
  rw [commits_append, tagged, committed, previous]
  simp only [handles, List.length_append, List.length_singleton, List.length_reverse,
    List.range_succ, List.map_append, List.map_singleton]
  rw [Nat.add_comm added.length first.length]

theorem rootHistory_of_session {Root : Type} {env : SEnv UImp} (roots : env.S → List Root)
    {profile : Numerics.Profile} {module_ : Module} {memory : Option Nat} {state : env.S}
    {start : Config Nat} {addrs : List Nat} {phase : Phase} {pending : Bool}
    {current : Config Nat × env.S} {tags : List CommitTag}
    (effect : ∀ prior call reply next, env.Ans prior call reply next →
      Publishes module_ call.target reply (roots prior) (roots next))
    (session : TSession profile env module_ memory roles start state addrs phase pending current tags) :
    RootHistory (roots state) (roots current.2) tags := by
  refine TSession.rec (motive := fun _ _ (current : Config Nat × env.S) tags _ =>
    RootHistory (roots state) (roots current.2) tags)
    ?base ?internal ?call ?answer ?invoke ?ret session
  case base => exact ⟨[], by simp, by simp [commits, handles]⟩
  case internal => intros; assumption
  case call =>
    intro phase config previous prior ctx address target args priorSession redex ih
    apply append_quiet ih
    cases calloutAt? module_ memory config <;> rfl
  case invoke => intros; exact append_quiet (by assumption) rfl
  case ret => intros; exact append_quiet (by assumption) rfl
  case answer =>
    intro phase config previous next prior ctx address target args reply priorSession redex answer ih
    rcases effect previous ⟨target, config.store, args⟩ reply next answer with
      ⟨unchanged, trapped⟩ | ⟨root, added, linked, returned⟩
    · rw [unchanged]
      apply append_quiet ih
      cases calloutAt? module_ memory config <;> simp [commits, Roles.answerTags, roles, trapped]
    · apply append_root ih added
      simp only [calloutAt?, redex, Option.bind_some]
      cases imp : module_.imports[target]? with
      | none => simp [imp] at linked
      | some imported => simp [commits, Roles.answerTags, roles, returned]

theorem history_of_session {profile : Numerics.Profile} {module_ : Module}
    {start : Config Nat} {addrs : List Nat} {phase : Phase} {pending : Bool}
    {current : Config Nat × World grow sig} {tags : List CommitTag}
    (linked : module_.imports[contract.code]?.isSome = true)
    (session : TSession profile (contract.env grow memory) module_ memory roles start state addrs
      phase pending current tags) : History state.writer current.2.writer tags := by
  refine rootHistory_of_session (fun (world : World grow sig) => world.writer.accepted) ?_ session
  intro prior call reply next answer
  change contract.answer memory prior call reply next at answer
  cases ran : contract.attempt memory prior call with
  | mk updated outcome =>
    simp only [Contract.answer, ran] at answer
    obtain ⟨rfl, rfl⟩ := answer
    cases outcome with
    | error issue => exact .inl ⟨congrArg Endpoints.State.accepted (refusal_keeps_writer ran), rfl⟩
    | ok handle =>
      obtain ⟨root, added, eqHandle, eqTarget⟩ := attempt_publishes ran
      exact .inr ⟨root, added, by simpa [eqTarget] using linked, by simp [eqHandle]⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core.Trace
