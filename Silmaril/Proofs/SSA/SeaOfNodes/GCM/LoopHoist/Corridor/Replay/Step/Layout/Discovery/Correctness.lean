module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Mathlib.Data.List.InsertIdx
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery
open Loop.MLIR.CF (Program TargetOp evalOp model)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : Layout.State Input saved carried result extra} {request : Nomination} {moved : Layout.Move state}
variable {reference : Step.State Input saved carried result extra}
variable {plan : Plan Input saved carried result} {budget : Nat}

theorem choose?_spec (chosen : choose? state = some (request, moved)) :
    request.origin ∈ state.reference.origins ∧ request.cut ≤ state.savedCount ∧
      Layout.emit? state request = some moved := by
  obtain ⟨cut, listed, picked⟩ := List.exists_of_findSome?_eq_some chosen
  obtain ⟨present, same, attempted⟩ := Replay.Discovery.choose?_spec picked
  refine ⟨present, same.symm ▸ Nat.le_of_lt_succ (List.mem_range.mp listed), ?_⟩
  cases raw : Layout.emit? state request with
  | none => simp [raw, tryMove] at attempted
  | some out =>
    simp [raw, tryMove] at attempted
    cases attempted
    rfl

theorem choose?_none_iff (valid : Layout.Invariant state) :
    choose? state = none ↔ ∀ request, Layout.emit? state request = none := by
  constructor
  · intro absent request
    cases attempted : Layout.emit? state request with
    | none => rfl
    | some outcome =>
      have present := List.mem_of_getElem? (Layout.emit?_placement attempted).1
      have checked := (Layout.emit?_spec attempted).2.1
      have cutIn : request.cut ∈ List.range (state.savedCount + 1) := by
        have inside := (of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1).2
        rw [Layout.savedCount_eq valid]
        exact List.mem_range.mpr (Nat.lt_succ_of_le inside)
      have failed := List.findSome?_eq_none_iff.mp absent request.cut cutIn
      have rejected := List.findSome?_eq_none_iff.mp failed request.origin present
      simp [tryMove, Except.toOption, attempted] at rejected
  · intro refused
    apply List.findSome?_eq_none_iff.mpr
    intro cut _
    apply List.findSome?_eq_none_iff.mpr
    intro origin _
    simp [tryMove, Except.toOption, refused]

theorem collect_replay (budget position : Nat) :
    Layout.run state position (collect state budget).requests = .ok (collect state budget).output := by
  induction budget generalizing extra position with
  | zero => rfl
  | succ budget ih =>
    cases picked : choose? state with
    | none => simp [collect, picked, Layout.run]
    | some pair =>
      rcases pair with ⟨request, moved⟩
      simpa only [collect, picked, Layout.run, (choose?_spec picked).2.2] using
        ih (state := moved.next) (position + 1)

theorem collect_stops (valid : Layout.Invariant state) (budget : Nat) :
    (collect state budget).requests.length ≤ budget ∧ (collect state budget).stopSpec budget := by
  induction budget generalizing extra with
  | zero =>
    cases picked : choose? state with
    | none =>
      have exhausted := (choose?_none_iff valid).mp picked
      simpa [collect, picked, Plan.stopSpec] using exhausted
    | some pair =>
      rcases pair with ⟨request, moved⟩
      simp [collect, picked, Plan.stopSpec]
      exact ⟨request, moved, (choose?_spec picked).2.2⟩
  | succ budget ih =>
    cases picked : choose? state with
    | none =>
      have eq : collect state (budget + 1) = ⟨[], ⟨extra, state⟩, .fixedPoint⟩ := by
        simp only [collect, picked]
      rw [eq]
      exact ⟨Nat.zero_le _, (choose?_none_iff valid).mp picked⟩
    | some pair =>
      rcases pair with ⟨request, moved⟩
      obtain ⟨bound, stopped⟩ := ih (Layout.emit?_invariant valid (choose?_spec picked).2.2)
      have eq : collect state (budget + 1) =
          ⟨request :: (collect moved.next budget).requests, (collect moved.next budget).output,
            (collect moved.next budget).stop⟩ := by
        simp only [collect, picked]
      rw [eq]
      refine ⟨Nat.succ_le_succ bound, ?_⟩
      cases stop : (collect moved.next budget).stop with
      | fixedPoint => simpa only [Plan.stopSpec, stop] using stopped
      | bound =>
        simp only [Plan.stopSpec, List.length_cons]
        simp only [Plan.stopSpec, stop] at stopped
        exact ⟨congrArg Nat.succ stopped.1, stopped.2⟩

private theorem emit_reduces (accepted : Layout.emit? state request = some moved) :
    moved.next.reference.origins.length + 1 = state.reference.origins.length := by
  obtain ⟨_, selected, _, _, _, erased, _⟩ := Step.emit_spec (Layout.emit?_spec accepted).1
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp selected
  change moved.append.next.origins.length + 1 = _
  rw [erased, List.length_eraseIdx_of_lt bound]
  omega

theorem collect_fixedPoint {budget : Nat} (enough : state.reference.origins.length ≤ budget) :
    (collect state budget).stop = .fixedPoint := by
  induction budget generalizing extra with
  | zero =>
    have empty := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
    have absent : choose? state = none := by
      simp only [choose?, empty, Replay.Discovery.choose?, List.findSome?_nil, List.findSome?_eq_none_iff]
      intro _ _
      trivial
    simp [collect, absent]
  | succ budget ih =>
    cases picked : choose? state with
    | none => simp [collect, picked]
    | some pair =>
      rcases pair with ⟨request, moved⟩
      have shrank := emit_reduces (choose?_spec picked).2.2
      simpa only [collect, picked] using ih (state := moved.next) (by omega)

private theorem discover_collect (accepted : discover reference budget = .ok plan) :
    ∃ state, Layout.initial? reference = some state ∧ supported? state = true ∧ plan = collect state budget := by
  simp only [discover] at accepted
  split at accepted
  next state initial =>
    split at accepted
    next supported =>
      cases accepted
      exact ⟨state, initial, supported, rfl⟩
    next => cases accepted
  next => cases accepted

theorem discover_spec (accepted : discover reference budget = .ok plan) (position : Nat) :
    ∃ state, Layout.initial? reference = some state ∧ supported? state = true ∧
      Layout.run state position plan.requests = .ok plan.output ∧ Layout.Invariant plan.output.2 ∧
      plan.requests.length ≤ budget ∧ plan.stopSpec budget := by
  obtain ⟨start, initial, supported, rfl⟩ := discover_collect accepted
  have valid := (Layout.initial?_spec initial).2
  have ran := collect_replay (state := start) budget position
  have final := (Layout.run_spec valid ran).1
  exact ⟨start, initial, supported, ran, final, collect_stops valid budget⟩

theorem discover_fixedPoint (accepted : discover reference budget = .ok plan)
    (enough : reference.origins.length ≤ budget) : plan.stop = .fixedPoint := by
  obtain ⟨start, initial, _, rfl⟩ := discover_collect accepted
  exact collect_fixedPoint (state := start) (by simpa only [(Layout.initial?_spec initial).1] using enough)

theorem discover_append_replay (accepted : discover reference budget = .ok plan) (position : Nat) :
    Step.run reference position (Layout.appendPlan (extra ++ [saved]).length plan.requests) =
      .ok ⟨plan.output.1, plan.output.2.reference⟩ := by
  obtain ⟨start, initial, _, ran, _⟩ := discover_spec accepted position
  obtain ⟨same, valid⟩ := Layout.initial?_spec initial
  simpa only [same] using (Layout.run_spec valid ran).2

theorem discover_packets (accepted : discover reference budget = .ok plan)
    {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {inventory : List Nat} {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : Saved.Invariant base reference.cfg inventory reference.origins reference.slots input values)
    (matched : Saved.Prefix.Matches reference.cfg.entry input values) :
    ∃ finalValues : Env (plan.output.1 ++ [saved]),
      Saved.Invariant base plan.output.2.cfg inventory plan.output.2.reference.origins
        plan.output.2.reference.slots input finalValues ∧
      Saved.Prefix.Matches plan.output.2.reference.cfg.entry input finalValues := by
  obtain ⟨start, initial, _, ran, _⟩ := discover_spec accepted 0
  obtain ⟨same, valid⟩ := Layout.initial?_spec initial
  exact Layout.run_packets valid (same ▸ prior) (same ▸ matched) ran

theorem discover_run_eq (accepted : discover reference budget = .ok plan) (input : Env Input) (fuel : Nat) :
    plan.output.2.cfg.run evalOp fuel input = plan.output.2.reference.cfg.run evalOp fuel input := by
  obtain ⟨_, _, _, _, valid, _⟩ := discover_spec accepted 0
  exact Layout.state_run_eq valid input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem discover_denotePart (accepted : discover reference budget = .ok plan) (input : Env Input) :
    (Cfg.embed plan.output.2.cfg).denotePart evalOp input =
      (Cfg.embed plan.output.2.reference.cfg).denotePart evalOp input := by
  obtain ⟨_, _, _, _, valid, _⟩ := discover_spec accepted 0
  exact Layout.state_denotePart valid input

theorem discover_fromTwo_budget {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    {g : Program Input carried result entrySigs headerSigs}
    {header : List Header.Pair.Request} {record : First Input carried result} {producer consumer : Nomination}
    {two : AfterReorder.Second.Emit.Emission Input carried result}
    {plan : Plan Input two.prepared.intermediate.1 carried result}
    (seed : Replay.replay g header [producer, consumer] = .ok (.two record consumer two))
    (accepted : discover (Step.fromTwo record consumer two) budget = .ok plan)
    (input : Env Input) (backedges : Nat) :
    plan.output.2.cfg.run evalOp (backedges + 3) input =
      (g.evalBackedges model backedges (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) := by
  obtain ⟨_, initial, _, ran, _⟩ := discover_spec accepted 2
  exact Layout.run_fromTwo_budget seed initial ran input backedges

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery
