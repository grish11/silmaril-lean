module

public import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Transcript.Defs
import Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Thms

public section

namespace Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Transcript

open Silmaril.Wasm Silmaril.Wasm.Game Silmaril.Wasm.Game.IOAccept Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Component.Engine
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored (Signature)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.Endpoints.Core (Contract)
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core
open Silmaril.Wasm.Game.HandleAccept.Wit.Stored.OwnedMemory.Claims.Core.Transcript

variable {sig : Signature} {grow : SingleThreaded.GrowOracle} {contract : Contract sig}
  {memory : Option Nat}

private theorem attempt_reference (prior : World grow sig) (call : UCall Nat) :
    (attempt contract memory prior call).1.reference = (load contract memory prior call).1 := by
  cases loaded : load contract memory prior call with
  | mk reference result =>
    simp only [attempt, loaded]
    split <;> rfl

theorem answer_effect {prior next : World grow sig} {call : UCall Nat} {reply : UReply}
    (answered : answer contract memory prior call reply next) :
    ∃ result, Effect contract memory prior next ⟨call, reply, result⟩ := by
  cases ran : attempt contract memory prior call with
  | mk updated result =>
    simp only [answer, ran] at answered
    obtain ⟨rfl, rfl⟩ := answered
    refine ⟨result, ran, rfl, ?_⟩
    cases result with
    | ok handle => exact ⟨rfl, success_publishes ran⟩
    | error issue =>
      refine ⟨rfl, refusal_keeps_writer ran, ?_⟩
      cases checked : preflight contract memory prior call with
      | error cause =>
        rw [preflight_refusal checked] at ran
        cases ran
        simp
      | ok args =>
        have reference := attempt_reference (contract := contract) (memory := memory) prior call
        simpa [checked, ran] using reference

theorem transcript_of_session {initial : World grow sig} {profile : Numerics.Profile} {module_ : Module}
    {start : Config Nat} {addrs : List Nat} {phase : Phase} {pending : Bool}
    {current : Config Nat × World grow sig} {tags : List Tag}
    (session : TSession profile (env contract grow memory) module_ memory roles start initial addrs
      phase pending current tags) :
    ∃ events, Timeline contract memory initial events current.2 ∧ visible module_ events = replies tags := by
  refine TSession.rec (motive := fun _ _ (current : Config Nat × World grow sig) tags _ =>
    ∃ events, Timeline contract memory initial events current.2 ∧ visible module_ events = replies tags)
    ?base ?internal ?call ?answer ?invoke ?ret session
  case base => exact ⟨[], .start, rfl⟩
  case internal => intros; assumption
  case call =>
    intro phase config prior tags ctx address target args priorSession redex ih
    obtain ⟨events, timeline, observed⟩ := ih
    refine ⟨events, timeline, ?_⟩
    cases calloutAt? module_ memory config <;> simpa [Roles.callTags, roles] using observed
  case answer =>
    intro phase config prior next tags ctx address target args reply priorSession redex answered ih
    obtain ⟨events, timeline, observed⟩ := ih
    obtain ⟨result, effect⟩ := answer_effect (contract := contract) (memory := memory) answered
    refine ⟨events ++ [⟨⟨target, config.store, args⟩, reply, result⟩], .answered timeline effect, ?_⟩
    simp only [visible, replies, List.filterMap_append, List.filterMap_cons, List.filterMap_nil,
      calloutAt?, redex, Option.bind_some]
    change visible module_ events ++ _ = replies tags ++ _
    rw [observed]
    cases module_.imports[target]? <;> simp [replies, Roles.answerTags, roles]
  case invoke =>
    intros
    obtain ⟨events, timeline, observed⟩ := ‹∃ _, _ ∧ _›
    exact ⟨events, timeline, by simpa [replies, List.filterMap_append] using observed⟩
  case ret =>
    intros
    obtain ⟨events, timeline, observed⟩ := ‹∃ _, _ ∧ _›
    exact ⟨events, timeline, by simpa [replies, List.filterMap_append] using observed⟩

end Silmaril.Proofs.Wasm.Game.HandleAccept.Wit.OwnedMemory.Claims.Transcript
