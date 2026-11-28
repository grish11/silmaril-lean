module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Mathlib.Data.List.InsertIdx
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopForest.Thms

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
variable {plan : Plan Input saved carried result} {budget : Nat} {policy : Policy}

private theorem mem_cuts {cut last : Nat} : cut ∈ policy.cuts last ↔ cut ≤ last := by
  cases policy <;> simp [Policy.cuts, Nat.lt_succ_iff]

private theorem emit_coordinates (valid : Layout.Invariant state) (accepted : Layout.emit? state request = some moved) :
    request.origin ∈ state.reference.origins ∧ request.cut ≤ state.savedCount := by
  have checked := (Layout.emit?_spec accepted).2.1
  have inside := (of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1).2
  exact ⟨List.mem_of_getElem? (Layout.emit?_placement accepted).1, (Layout.savedCount_eq valid).symm ▸ inside⟩

theorem mem_acceptedCuts_iff (valid : Layout.Invariant state) (origin cut : Nat) :
    cut ∈ acceptedCuts state origin ↔ ∃ moved, Layout.emit? state ⟨origin, cut⟩ = some moved := by
  rw [Layout.Discovery.acceptedCuts, List.mem_filter]
  constructor
  · rintro ⟨_, checked⟩
    cases emitted : Layout.emit? state ⟨origin, cut⟩ with
    | none => simp [emitted] at checked
    | some moved => exact ⟨moved, rfl⟩
  · rintro ⟨moved, emitted⟩
    exact ⟨mem_cuts.mpr (emit_coordinates valid emitted).2, by simp [emitted]⟩

theorem chooseWith?_spec (chosen : chooseWith? policy state = some (request, moved)) :
    request.origin ∈ state.reference.origins ∧ request.cut ≤ state.savedCount ∧
      Layout.emit? state request = some moved := by
  obtain ⟨cut, listed, picked⟩ := List.exists_of_findSome?_eq_some chosen
  obtain ⟨present, same, attempted⟩ := Replay.Discovery.choose?_spec picked
  refine ⟨present, same.symm ▸ mem_cuts.mp listed, ?_⟩
  cases raw : Layout.emit? state request with
  | none => simp [raw, tryMove] at attempted
  | some out =>
    simp [raw, tryMove] at attempted
    cases attempted
    rfl

theorem chooseWith?_none_iff (valid : Layout.Invariant state) :
    chooseWith? policy state = none ↔ ∀ request, Layout.emit? state request = none := by
  constructor
  · intro absent request
    cases attempted : Layout.emit? state request with
    | none => rfl
    | some outcome =>
      obtain ⟨present, inside⟩ := emit_coordinates valid attempted
      have failed := List.findSome?_eq_none_iff.mp absent request.cut (mem_cuts.mpr inside)
      have rejected := List.findSome?_eq_none_iff.mp failed request.origin present
      simp [tryMove, Except.toOption, attempted] at rejected
  · intro refused
    apply List.findSome?_eq_none_iff.mpr
    intro cut _
    apply List.findSome?_eq_none_iff.mpr
    intro origin _
    simp [tryMove, Except.toOption, refused]

private theorem cuts_ordered (policy : Policy) (last : Nat) : (policy.cuts last).Pairwise policy.Preferred := by
  cases policy with
  | earliest => exact List.pairwise_le_range
  | latest => exact List.pairwise_reverse.mpr List.pairwise_le_range

theorem chooseWith?_extremal (valid : Layout.Invariant state) (chosen : chooseWith? policy state = some (request, moved))
    {other : Nomination} {alternative : Layout.Move state} (accepted : Layout.emit? state other = some alternative) :
    policy.Preferred request.cut other.cut := by
  obtain ⟨before, cut, after, order, picked, rejected⟩ := List.findSome?_eq_some_iff.mp chosen
  have atCut := (Replay.Discovery.choose?_spec picked).2.1
  obtain ⟨present, inside⟩ := emit_coordinates valid accepted
  have inCuts : other.cut ∈ policy.cuts state.savedCount := mem_cuts.mpr inside
  have survived : other.cut ∉ before := by
    intro earlier
    have refused := List.findSome?_eq_none_iff.mp (rejected _ earlier) other.origin present
    rcases other with ⟨origin, cut⟩
    simp [tryMove, Except.toOption, accepted] at refused
  rw [order] at inCuts
  have later := (List.mem_append.mp inCuts).resolve_left survived
  rw [atCut]
  rcases List.mem_cons.mp later with same | inTail
  · rw [same]
    cases policy <;> exact Nat.le_refl _
  · have sorted := cuts_ordered policy state.savedCount
    rw [order] at sorted
    exact (List.pairwise_cons.mp (List.pairwise_append.mp sorted).2.1).1 _ inTail

private theorem toLatch_ne_header {edge : NaturalLoop.Backedge (Label saved carried result extra)}
    {b : BlockId (Label saved carried result extra)} (path : NaturalLoop.ToLatch state.cfg edge b) :
    b ≠ some edge.header := by
  cases path with
  | latch _ avoids => exact fun same => avoids (Option.some.inj same)
  | predecessor _ avoids _ _ _ => exact avoids

private theorem toLatch_dominated {edge : NaturalLoop.Backedge (Label saved carried result extra)}
    {b : BlockId (Label saved carried result extra)} (path : NaturalLoop.ToLatch state.cfg edge b)
    (dom : Dominates state.cfg (some edge.header) (some edge.latch)) : Dominates state.cfg (some edge.header) b := by
  induction path with
  | latch => exact dom
  | predecessor _ _ slot actual tail ih =>
    intro past reachable
    have includes := ih _ (.step reachable slot actual)
    exact (List.mem_cons.mp includes).resolve_left (Ne.symm (toLatch_ne_header tail))

theorem preheader_depth_eq_zero {tree : DominatorTree state.cfg}
    {loops : List (LoopForest.HeaderLoop (Label saved carried result extra))}
    (forest : LoopForest.forest? tree AfterReorder.Second.intermediateBlocks = some loops)
    (complete : tree.Complete) : LoopForest.depth tree loops none = 0 := by
  let _ := NaturalLoop.blockDecEq tree
  have listed := ((LoopForest.forest_eq_some_iff loops).mp forest).1
  have empty : LoopForest.enclosing tree loops none = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro loop member
    have ⟨inForest, inside⟩ := List.mem_filter.mp member
    obtain ⟨edge, actual, _, inLoop⟩ := (LoopForest.mem_loop_iff listed complete inForest none).mp
      (of_decide_eq_true inside)
    rcases inLoop with impossible | path
    · cases impossible
    · have entryDominated := toLatch_dominated path actual.2.2 _ .entry
      simp at entryDominated
  simp [LoopForest.depth, empty]

theorem collectWith_replay (policy : Policy) (budget position : Nat) :
    Layout.run state position (collectWith policy state budget).requests = .ok (collectWith policy state budget).output := by
  induction budget generalizing extra position with
  | zero => rfl
  | succ budget ih =>
    cases picked : chooseWith? policy state with
    | none => simp [collectWith, picked, Layout.run]
    | some pair =>
      rcases pair with ⟨request, moved⟩
      simpa only [collectWith, picked, Layout.run, (chooseWith?_spec picked).2.2] using
        ih (state := moved.next) (position + 1)

theorem collectWith_stops (policy : Policy) (valid : Layout.Invariant state) (budget : Nat) :
    (collectWith policy state budget).requests.length ≤ budget ∧ (collectWith policy state budget).stopSpec budget := by
  induction budget generalizing extra with
  | zero =>
    cases picked : chooseWith? policy state with
    | none =>
      have exhausted := (chooseWith?_none_iff valid).mp picked
      simpa [collectWith, picked, Plan.stopSpec] using exhausted
    | some pair =>
      rcases pair with ⟨request, moved⟩
      simp [collectWith, picked, Plan.stopSpec]
      exact ⟨request, moved, (chooseWith?_spec picked).2.2⟩
  | succ budget ih =>
    cases picked : chooseWith? policy state with
    | none =>
      have eq : collectWith policy state (budget + 1) = ⟨[], ⟨extra, state⟩, .fixedPoint⟩ := by
        simp only [collectWith, picked]
      rw [eq]
      exact ⟨Nat.zero_le _, (chooseWith?_none_iff valid).mp picked⟩
    | some pair =>
      rcases pair with ⟨request, moved⟩
      obtain ⟨bound, stopped⟩ := ih (Layout.emit?_invariant valid (chooseWith?_spec picked).2.2)
      have eq : collectWith policy state (budget + 1) =
          ⟨request :: (collectWith policy moved.next budget).requests, (collectWith policy moved.next budget).output,
            (collectWith policy moved.next budget).stop⟩ := by
        simp only [collectWith, picked]
      rw [eq]
      refine ⟨Nat.succ_le_succ bound, ?_⟩
      cases stop : (collectWith policy moved.next budget).stop with
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

theorem collectWith_fixedPoint {budget : Nat} (enough : state.reference.origins.length ≤ budget) :
    (collectWith policy state budget).stop = .fixedPoint := by
  induction budget generalizing extra with
  | zero =>
    have empty := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero enough)
    have absent : chooseWith? policy state = none := by
      simp only [chooseWith?, empty, Replay.Discovery.choose?, List.findSome?_nil, List.findSome?_eq_none_iff]
      intro _ _
      trivial
    simp [collectWith, absent]
  | succ budget ih =>
    cases picked : chooseWith? policy state with
    | none => simp [collectWith, picked]
    | some pair =>
      rcases pair with ⟨request, moved⟩
      have shrank := emit_reduces (chooseWith?_spec picked).2.2
      simpa only [collectWith, picked] using ih (state := moved.next) (by omega)

private theorem discoverWith_collect (accepted : discoverWith policy reference budget = .ok plan) :
    ∃ state, Layout.initial? reference = some state ∧ supported? state = true ∧ plan = collectWith policy state budget := by
  simp only [discoverWith] at accepted
  split at accepted
  next state initial =>
    split at accepted
    next supported =>
      cases accepted
      exact ⟨state, initial, supported, rfl⟩
    next => cases accepted
  next => cases accepted

theorem discoverWith_spec (accepted : discoverWith policy reference budget = .ok plan) (position : Nat) :
    ∃ state, Layout.initial? reference = some state ∧ supported? state = true ∧
      Layout.run state position plan.requests = .ok plan.output ∧ Layout.Invariant plan.output.2 ∧
      plan.requests.length ≤ budget ∧ plan.stopSpec budget := by
  obtain ⟨start, initial, supported, rfl⟩ := discoverWith_collect accepted
  have valid := (Layout.initial?_spec initial).2
  have ran := collectWith_replay (state := start) policy budget position
  have final := (Layout.run_spec valid ran).1
  exact ⟨start, initial, supported, ran, final, collectWith_stops policy valid budget⟩

theorem discoverWith_fixedPoint (accepted : discoverWith policy reference budget = .ok plan)
    (enough : reference.origins.length ≤ budget) : plan.stop = .fixedPoint := by
  obtain ⟨start, initial, _, rfl⟩ := discoverWith_collect accepted
  exact collectWith_fixedPoint (state := start) (by simpa only [(Layout.initial?_spec initial).1] using enough)

theorem discoverWith_append_replay (accepted : discoverWith policy reference budget = .ok plan) (position : Nat) :
    Step.run reference position (Layout.appendPlan (extra ++ [saved]).length plan.requests) =
      .ok ⟨plan.output.1, plan.output.2.reference⟩ := by
  obtain ⟨start, initial, _, ran, _⟩ := discoverWith_spec accepted position
  obtain ⟨same, valid⟩ := Layout.initial?_spec initial
  simpa only [same] using (Layout.run_spec valid ran).2

theorem discoverWith_packets (accepted : discoverWith policy reference budget = .ok plan)
    {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {inventory : List Nat} {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : Saved.Invariant base reference.cfg inventory reference.origins reference.slots input values)
    (matched : Saved.Prefix.Matches reference.cfg.entry input values) :
    ∃ finalValues : Env (plan.output.1 ++ [saved]),
      Saved.Invariant base plan.output.2.cfg inventory plan.output.2.reference.origins
        plan.output.2.reference.slots input finalValues ∧
      Saved.Prefix.Matches plan.output.2.reference.cfg.entry input finalValues := by
  obtain ⟨start, initial, _, ran, _⟩ := discoverWith_spec accepted 0
  obtain ⟨same, valid⟩ := Layout.initial?_spec initial
  exact Layout.run_packets valid (same ▸ prior) (same ▸ matched) ran

theorem discoverWith_run_eq (accepted : discoverWith policy reference budget = .ok plan) (input : Env Input) (fuel : Nat) :
    plan.output.2.cfg.run evalOp fuel input = plan.output.2.reference.cfg.run evalOp fuel input := by
  obtain ⟨_, _, _, _, valid, _⟩ := discoverWith_spec accepted 0
  exact Layout.state_run_eq valid input fuel

private theorem appendPlan_congr {left right : List Nomination} (count : Nat)
    (same : left.map Nomination.origin = right.map Nomination.origin) :
    Layout.appendPlan count left = Layout.appendPlan count right := by
  induction left generalizing count right with
  | nil => cases right <;> simp_all [Layout.appendPlan]
  | cons request rest ih =>
    cases right with
    | nil => simp at same
    | cons other tail =>
      obtain ⟨origin, remaining⟩ := List.cons.inj same
      change (⟨request.origin, count⟩ : Nomination) :: Layout.appendPlan (count + 1) rest =
        ⟨other.origin, count⟩ :: Layout.appendPlan (count + 1) tail
      rw [origin, ih _ remaining]

theorem discoverWith_reference_eq {otherPolicy : Policy} {otherBudget : Nat}
    {otherPlan : Plan Input saved carried result}
    (left : discoverWith policy reference budget = .ok plan)
    (right : discoverWith otherPolicy reference otherBudget = .ok otherPlan)
    (same : plan.requests.map Nomination.origin = otherPlan.requests.map Nomination.origin) :
    (⟨plan.output.1, plan.output.2.reference⟩ : Step.Output Input saved carried result) =
      ⟨otherPlan.output.1, otherPlan.output.2.reference⟩ := by
  have common := discoverWith_append_replay left 0
  rw [appendPlan_congr _ same, discoverWith_append_replay right 0] at common
  exact (Except.ok.inj common).symm

theorem discoverWith_sameOrigins_run_eq {otherPolicy : Policy} {otherBudget : Nat}
    {otherPlan : Plan Input saved carried result}
    (left : discoverWith policy reference budget = .ok plan)
    (right : discoverWith otherPolicy reference otherBudget = .ok otherPlan)
    (same : plan.requests.map Nomination.origin = otherPlan.requests.map Nomination.origin)
    (input : Env Input) (fuel : Nat) :
    plan.output.2.cfg.run evalOp fuel input = otherPlan.output.2.cfg.run evalOp fuel input :=
  (discoverWith_run_eq left input fuel).trans
    ((congrArg (fun out : Step.Output Input saved carried result => out.2.cfg.run evalOp fuel input)
      (discoverWith_reference_eq left right same)).trans (discoverWith_run_eq right input fuel).symm)

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem discoverWith_denotePart (accepted : discoverWith policy reference budget = .ok plan) (input : Env Input) :
    (Cfg.embed plan.output.2.cfg).denotePart evalOp input =
      (Cfg.embed plan.output.2.reference.cfg).denotePart evalOp input := by
  obtain ⟨_, _, _, _, valid, _⟩ := discoverWith_spec accepted 0
  exact Layout.state_denotePart valid input

theorem discoverWith_fromTwo_budget {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    {g : Program Input carried result entrySigs headerSigs}
    {header : List Header.Pair.Request} {record : First Input carried result} {producer consumer : Nomination}
    {two : AfterReorder.Second.Emit.Emission Input carried result}
    {plan : Plan Input two.prepared.intermediate.1 carried result}
    (seed : Replay.replay g header [producer, consumer] = .ok (.two record consumer two))
    (accepted : discoverWith policy (Step.fromTwo record consumer two) budget = .ok plan)
    (input : Env Input) (backedges : Nat) :
    plan.output.2.cfg.run evalOp (backedges + 3) input =
      (g.evalBackedges model backedges (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) := by
  obtain ⟨_, initial, _, ran, _⟩ := discoverWith_spec accepted 2
  exact Layout.run_fromTwo_budget seed initial ran input backedges

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Discovery
