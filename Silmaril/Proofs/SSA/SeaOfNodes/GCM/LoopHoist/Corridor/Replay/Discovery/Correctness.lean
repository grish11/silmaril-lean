module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Defs
import Mathlib.Data.List.InsertIdx
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery

open Silmaril.MLIR.Arith (Width)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery
open Header.Earlier (Operation operations)
open Loop.MLIR.CF (Program lower)

variable {Input extra : List Width} {saved carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {state : Step.State Input saved carried result extra}

theorem choose?_spec {α : Type} {origins : List Nat} {cut : Nat} {tryMove : Nomination → Except Reason α}
    {request : Nomination} {out : α} (chosen : choose? origins cut tryMove = some (request, out)) :
    request.origin ∈ origins ∧ request.cut = cut ∧ tryMove request = .ok out := by
  obtain ⟨origin, present, checked⟩ := List.exists_of_findSome?_eq_some chosen
  cases attempted : tryMove ⟨origin, cut⟩ with
  | error reason => simp [attempted, Except.toOption] at checked
  | ok next =>
    simp [attempted, Except.toOption] at checked
    obtain ⟨rfl, rfl⟩ := checked
    exact ⟨present, rfl, attempted⟩

private theorem choose?_none {α : Type} {origins : List Nat} {cut : Nat} {tryMove : Nomination → Except Reason α}
    (bounds : ∀ {rq out}, tryMove rq = .ok out → rq.origin ∈ origins ∧ rq.cut = cut) :
    choose? origins cut tryMove = none ↔ ∀ rq, ∃ reason, tryMove rq = .error reason := by
  constructor
  · intro rejected request
    cases checked : tryMove request with
    | error reason => exact ⟨reason, rfl⟩
    | ok next =>
      obtain ⟨present, site⟩ := bounds checked
      rcases request with ⟨origin, coordinate⟩
      change coordinate = cut at site
      subst coordinate
      have absent := List.findSome?_eq_none_iff.mp rejected origin present
      simp [checked, Except.toOption] at absent
  · intro rejected
    apply List.findSome?_eq_none_iff.mpr
    intro origin _
    obtain ⟨reason, checked⟩ := rejected ⟨origin, cut⟩
    simp [checked, Except.toOption]

private theorem firstMove?_none {before : Header.Sequence.State Input carried result} :
    firstMove? before = none ↔ ∀ request, ∃ reason, Replay.first? before request = .error reason := by
  apply choose?_none
  intro request out checked
  obtain ⟨_, _, cut, selected, _⟩ := first?_spec checked
  exact ⟨List.mem_of_getElem? selected, cut⟩

private theorem secondMove?_none {first : First Input carried result} :
    secondMove? first = none ↔ ∀ request, ∃ reason, Replay.second? first request = .error reason := by
  apply choose?_none
  intro request out checked
  have cut := congrArg GCM.Point.cut (second?_spec checked).1
  exact ⟨List.mem_of_getElem? (second?_current checked).2.2, cut⟩

theorem laterMove?_none :
    laterMove? state = none ↔ ∀ request, ∃ reason, Step.emit state request = .error reason := by
  apply choose?_none
  intro request out checked
  obtain ⟨cut, selected, _⟩ := Step.emit_spec checked
  exact ⟨List.mem_of_getElem? selected, cut⟩

theorem next?_none_iff (out : Step.Result Input carried result) :
    next? out = none ↔ Exhausted out := by
  cases out with
  | initial snapshot =>
    cases snapshot with
    | zero => simpa only [next?, Exhausted, Option.map_eq_none_iff] using firstMove?_none
    | one => simpa only [next?, Exhausted, Option.map_eq_none_iff] using secondMove?_none
    | two => simpa only [next?, Exhausted, Option.map_eq_none_iff] using laterMove?_none
  | extended => simpa only [next?, Exhausted, Option.map_eq_none_iff] using laterMove?_none

private theorem emit_reduces {request : Nomination} {moved : Step.Emission Input saved carried result extra}
    (checked : Step.emit state request = .ok moved) :
    moved.next.origins.length + 1 = state.origins.length := by
  obtain ⟨_, selected, _, _, _, erased, _⟩ := Step.emit_spec checked
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp selected
  rw [erased, List.length_eraseIdx_of_lt bound]
  omega

theorem collect_replay (budget position : Nat) :
    Step.run state position (collect state budget).requests = .ok (collect state budget).output := by
  induction budget generalizing extra position with
  | zero => rfl
  | succ budget ih =>
    cases step : laterMove? state with
    | none => simp [collect, step, Step.run]
    | some pair =>
      rcases pair with ⟨request, moved⟩
      have checked := (choose?_spec step).2.2
      simpa only [collect, step, Step.run, checked] using ih (state := moved.next) (position + 1)

theorem collect_count (budget : Nat) :
    (collect state budget).output.2.origins.length + (collect state budget).requests.length =
      state.origins.length := by
  induction budget generalizing extra with
  | zero => rfl
  | succ budget ih =>
    cases step : laterMove? state with
    | none =>
      have done : collect state (budget + 1) = ⟨[], ⟨extra, state⟩⟩ := by simp only [collect, step]
      rw [done]
      rfl
    | some pair =>
      rcases pair with ⟨request, moved⟩
      have reduced := emit_reduces (choose?_spec step).2.2
      have done : collect state (budget + 1) =
          ⟨request :: (collect moved.next budget).requests, (collect moved.next budget).output⟩ := by
        simp only [collect, step]
      rw [done]
      simpa only [List.length_cons, ← Nat.add_assoc, ih (state := moved.next)] using reduced

theorem collect_exhausted {budget : Nat} (enough : state.origins.length ≤ budget) :
    laterMove? (collect state budget).output.2 = none := by
  induction budget generalizing extra with
  | zero =>
    have empty : state.origins = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
    simp [collect, laterMove?, choose?, empty]
  | succ budget ih =>
    cases step : laterMove? state with
    | none =>
      have done : collect state (budget + 1) = ⟨[], ⟨extra, state⟩⟩ := by simp only [collect, step]
      rw [done]
      exact step
    | some pair =>
      rcases pair with ⟨request, moved⟩
      have reduced := emit_reduces (choose?_spec step).2.2
      have done : collect state (budget + 1) =
          ⟨request :: (collect moved.next budget).requests, (collect moved.next budget).output⟩ := by
        simp only [collect, step]
      rw [done]
      exact ih (state := moved.next) (by omega)

theorem collect_origins {original : List Operation} (budget : Nat)
    (aligned : state.origins.map (fun origin => original[origin]?) = (operations (state.cfg.block .header)).map some) :
    (collect state budget).output.2.origins.map (fun origin => original[origin]?) =
      (operations ((collect state budget).output.2.cfg.block .header)).map some := by
  induction budget generalizing extra with
  | zero => exact aligned
  | succ budget ih =>
    cases step : laterMove? state with
    | none =>
      have done : collect state (budget + 1) = ⟨[], ⟨extra, state⟩⟩ := by simp only [collect, step]
      rw [done]
      exact aligned
    | some pair =>
      rcases pair with ⟨request, moved⟩
      have checked := (choose?_spec step).2.2
      obtain ⟨_, _, _, _, emitted, erased, _⟩ := Step.emit_spec checked
      have order := AfterReorder.Second.Emit.emitAt?_operations emitted
      have nextAligned : moved.next.origins.map (fun origin => original[origin]?) =
          (operations (moved.next.cfg.block .header)).map some := by
        rw [erased, ← List.eraseIdx_map, aligned, List.eraseIdx_map, order]
      have done : collect state (budget + 1) =
          ⟨request :: (collect moved.next budget).requests, (collect moved.next budget).output⟩ := by
        simp only [collect, step]
      rw [done]
      exact ih nextAligned

theorem discover_spec {g : Program Input carried result entrySigs headerSigs}
    {header : List Header.Pair.Request} {plan : Plan Input carried result}
    (accepted : discover g header = .ok plan) :
    Step.replayAll g header plan.requests = .ok plan.output ∧ Exhausted plan.output ∧
      plan.output.origins.map (fun origin => (operations ((lower g).block .header))[origin]?) =
        (headerOperations plan.output).map some := by
  cases ran : Header.Sequence.run? (Header.Sequence.initial (lower g)) header with
  | none => simp [discover, ran] at accepted
  | some before =>
    cases firstChecked : firstMove? before with
    | none =>
      simp [discover, ran, firstChecked] at accepted
      subst plan
      have seeded : Replay.replay g header [] = .ok (.zero before) := by
        simp [Replay.replay, ran, Replay.run]
      exact ⟨by simp [Step.replayAll, seeded, Except.map],
        firstMove?_none.mp firstChecked, replay_origins seeded⟩
    | some pair =>
      rcases pair with ⟨producer, first⟩
      have firstEmits := (choose?_spec firstChecked).2.2
      cases secondChecked : secondMove? first with
      | none =>
        simp [discover, ran, firstChecked, secondChecked] at accepted
        subst plan
        have seeded : Replay.replay g header [producer] = .ok (.one first) := by
          simp [Replay.replay, ran, Replay.run, Replay.advance, firstEmits, Except.map]
        exact ⟨by simp [Step.replayAll, seeded, Except.map], secondMove?_none.mp secondChecked, replay_origins seeded⟩
      | some pair =>
        rcases pair with ⟨consumer, two⟩
        have secondEmits := (choose?_spec secondChecked).2.2
        have seeded : Replay.replay g header [producer, consumer] = .ok (.two first consumer two) := by
          simp [Replay.replay, ran, Replay.run, Replay.advance, firstEmits, secondEmits, Except.map]
        let state := Step.fromTwo first consumer two
        let suffix := collect state state.origins.length
        have replayed := collect_replay (state := state) state.origins.length 2
        have exhausted := collect_exhausted (state := state) (Nat.le_refl state.origins.length)
        change Step.run state 2 suffix.requests = .ok suffix.output at replayed
        change laterMove? suffix.output.2 = none at exhausted
        have accepted' : finish producer consumer first two suffix = plan := by
          simpa only [discover, ran, firstChecked, secondChecked, Except.ok.injEq] using accepted
        cases requests : suffix.requests with
        | nil =>
          simp only [finish, requests] at accepted'
          subst plan
          have same : ⟨_, state⟩ = suffix.output := by
            simpa only [requests, Step.run, Except.ok.injEq] using replayed
          rw [← same] at exhausted
          exact ⟨by simp [Step.replayAll, seeded, Except.map], laterMove?_none.mp exhausted, replay_origins seeded⟩
        | cons request rest =>
          simp only [finish, requests] at accepted'
          subst plan
          have continued : Step.run state 2 (request :: rest) = .ok suffix.output := by
            simpa only [requests] using replayed
          change Step.run (Step.fromTwo first consumer two) 2 (request :: rest) = .ok suffix.output at continued
          exact ⟨by simp [Step.replayAll, seeded, continued, Except.map], laterMove?_none.mp exhausted,
            collect_origins (state := state) state.origins.length (replay_origins seeded)⟩

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery
