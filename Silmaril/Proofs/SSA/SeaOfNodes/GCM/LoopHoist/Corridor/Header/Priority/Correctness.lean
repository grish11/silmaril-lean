module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist (SourceLabel)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier (Operation operations)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair (Request)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence (State)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {state next : State Input carried result}
variable {out : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {index origin : Nat} {request : Request} {requests : List Request} {priorities : List Nat}

theorem resolve?_sound (resolved : resolve? state origin = some index) :
    state.origins[index]? = some origin := by
  obtain ⟨bound, eq, _⟩ := List.idxOf?_eq_some_iff.mp resolved
  exact List.getElem?_eq_some_iff.mpr ⟨bound, eq⟩

theorem choose?_earliest (found : choose? state index = some (request, next)) :
    request.binding = index ∧ request.cut < index ∧ Header.Sequence.step? state request = some next ∧
      ∀ cut < request.cut, Header.Sequence.step? state ⟨index, cut⟩ = none := by
  obtain ⟨pre, chosen, post, layout, selected, earlier⟩ := List.findSome?_eq_some_iff.mp found
  obtain ⟨_, stepped, eq⟩ := Option.map_eq_some_iff.mp selected
  cases eq
  have inRange : pre.length < index := by
    have lengths := congrArg List.length layout
    simp only [List.length_range, List.length_append, List.length_cons] at lengths
    omega
  have atCut := congrArg (fun cuts : List Nat => cuts[pre.length]?) layout
  rw [List.getElem?_range inRange, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at atCut
  have position : pre.length = chosen := Option.some.inj atCut
  refine ⟨rfl, position ▸ inRange, stepped, ?_⟩
  intro cut earlierCut
  have earlierIndex : cut < pre.length := position.symm ▸ earlierCut
  have atEarlier := congrArg (fun cuts : List Nat => cuts[cut]?) layout
  rw [List.getElem?_range (Nat.lt_trans earlierIndex inRange), List.getElem?_append_left earlierIndex]
    at atEarlier
  have refused := earlier cut (List.mem_of_getElem? atEarlier.symm)
  exact Option.map_eq_none_iff.mp refused

theorem choose?_eq_none : choose? state index = none ↔
    ∀ cut < index, Header.Sequence.step? state ⟨index, cut⟩ = none := by
  simp [choose?, List.findSome?_eq_none_iff]

theorem plan?_replay (planned : plan? state priorities = some (requests, next)) :
    Header.Sequence.run? state requests = some next := by
  induction priorities generalizing state requests with
  | nil =>
    cases planned
    rfl
  | cons origin rest ih =>
    obtain ⟨index, _, advanced⟩ := Option.bind_eq_some_iff.mp planned
    cases chosen : choose? state index with
    | none => exact ih (by simpa only [chosen] using advanced)
    | some pair =>
      obtain ⟨request, middle⟩ := pair
      simp only [chosen] at advanced
      obtain ⟨⟨tail, last⟩, followed, eq⟩ := Option.bind_eq_some_iff.mp advanced
      cases eq
      have emitted := (choose?_earliest chosen).2.2.1
      simp only [Header.Sequence.run?, emitted, Option.bind_some]
      exact ih followed

private theorem plan?_exists {source : List Operation} (tracked : Header.Sequence.Tracked source state)
    (known : ∀ origin ∈ priorities, origin < source.length) :
    ∃ result, plan? state priorities = some result := by
  induction priorities generalizing state with
  | nil => exact ⟨([], state), rfl⟩
  | cons origin rest ih =>
    have present : origin ∈ state.origins :=
      tracked.1.mem_iff.mpr (List.mem_range.mpr (known origin (by simp)))
    have tailKnown : ∀ id ∈ rest, id < source.length :=
      fun id member => known id (List.mem_cons_of_mem _ member)
    cases resolved : resolve? state origin with
    | none => exact ((List.idxOf?_eq_none_iff.mp resolved) present).elim
    | some index =>
      cases chosen : choose? state index with
      | none =>
        obtain ⟨result, planned⟩ := ih tracked tailKnown
        exact ⟨result, by simp [plan?, resolved, chosen, planned]⟩
      | some pair =>
        obtain ⟨request, middle⟩ := pair
        have stepped := (choose?_earliest chosen).2.2.1
        have middleTracked := Header.Sequence.run?_tracked tracked
          (by simp [Header.Sequence.run?, stepped] :
            Header.Sequence.run? state [request] = some middle)
        obtain ⟨⟨tail, final⟩, followed⟩ := ih middleTracked tailKnown
        exact ⟨(request :: tail, final), by simp [plan?, resolved, chosen, followed]⟩

theorem schedule?_exists (distinct : priorities.Nodup)
    (known : ∀ origin ∈ priorities, origin < (operations ((lower g).block .header)).length) :
    ∃ requests out, schedule? g priorities = some (requests, out) := by
  obtain ⟨⟨requests, final⟩, planned⟩ := plan?_exists (Header.Sequence.initial_tracked (lower g)) known
  exact ⟨requests, final.cfg, by simp [schedule?, distinct, planned]⟩

theorem schedule?_replay (accepted : schedule? g priorities = some (requests, out)) :
    Header.Sequence.schedule? g requests = some out := by
  by_cases distinct : priorities.Nodup
  · simp only [schedule?, ite_eq_left distinct] at accepted
    obtain ⟨⟨_, final⟩, planned, eq⟩ := Option.map_eq_some_iff.mp accepted
    cases eq
    simp only [Header.Sequence.schedule?, plan?_replay planned, Option.map_some]
  · simp [schedule?, distinct] at accepted

theorem schedule?_frames (accepted : schedule? g priorities = some (requests, out)) (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) :=
  Header.Sequence.schedule?_frames (schedule?_replay accepted) input

theorem schedule?_run_eq (accepted : schedule? g priorities = some (requests, out)) (input : Env Input)
    (fuel : Nat) : out.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Header.Sequence.schedule?_run_eq (schedule?_replay accepted) input fuel

theorem schedule?_budget (accepted : schedule? g priorities = some (requests, out))
    (input : Env Input) (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Header.Sequence.schedule?_budget (schedule?_replay accepted) input budget

theorem schedule?_denotePart (accepted : schedule? g priorities = some (requests, out)) (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input :=
  Header.Sequence.schedule?_denotePart (schedule?_replay accepted) input

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority
