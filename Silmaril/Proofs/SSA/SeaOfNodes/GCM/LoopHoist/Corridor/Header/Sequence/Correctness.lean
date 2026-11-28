module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Mathlib.Data.List.Perm.Basic
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header
  (withHeader withHeader_frames withHeader_run_eq withHeader_denotePart)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier (Operation operations)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair (Request)
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence
open Loop.MLIR.CF (Program TargetOp evalOp lower model lower_run)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {cfg out : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {state next : State Input carried result} {request : Request} {requests : List Request}

private theorem getAtPrefix {α : Type} (pre : List α) (chosen : α) (suf : List α) :
    (pre ++ chosen :: suf)[pre.length]? = some chosen := by
  rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

private theorem eraseAtPrefix {α : Type} (pre : List α) (chosen : α) (suf : List α) :
    (pre ++ chosen :: suf).eraseIdx pre.length = pre ++ suf := by
  rw [List.eraseIdx_append_of_length_le (Nat.le_refl _), Nat.sub_self]
  rfl

private theorem insertAtPrefix {α : Type} (pre : List α) (chosen : α) (suf : List α) :
    (pre ++ suf).insertIdx pre.length chosen = pre ++ chosen :: suf := by
  induction pre with
  | nil => rfl
  | cons _ _ ih => simp only [List.cons_append, List.length_cons, List.insertIdx_succ_cons, ih]

theorem move?_transport (moved : Header.Pair.move? cfg request = some out) :
    ∃ chosen : Operation,
      (operations (cfg.block .header))[request.binding]? = some chosen ∧
      operations (out.block .header) = relocate request chosen (operations (cfg.block .header)) ∧
      request.insertion < (operations (cfg.block .header)).length := by
  by_cases earlier : request.insertion < request.binding
  · have checked := Header.Pair.move?_checked moved
    have emitted : Header.Earlier.moveAt? cfg request.binding request.point = some out := by
      simpa [Header.Pair.move?, earlier, checked] using moved
    obtain ⟨pre, crossed, chosen, suf, dest, index, oldOrder, newOrder⟩ :=
      Header.Earlier.moveAt?_order emitted
    change pre.length = request.insertion at dest
    have loc : (pre ++ crossed).length = request.binding := by simpa only [List.length_append] using index
    refine ⟨chosen, ?_, ?_, ?_⟩
    · rw [oldOrder, ← loc, getAtPrefix]
    · unfold relocate
      rw [oldOrder, ← loc, ← dest, eraseAtPrefix, List.append_assoc, insertAtPrefix]
      exact newOrder
    · rw [oldOrder]
      simp only [List.length_append, List.length_cons]
      omega
  · have emitted : Header.Later.moveCfgAt? cfg request.binding request.point = some out := by
      simpa [Header.Pair.move?, earlier] using moved
    obtain ⟨pre, crossed, chosen, suf, index, dest, oldOrder, newOrder⟩ :=
      Header.Later.moveCfgAt?_order emitted
    change pre.length + crossed.length = request.insertion at dest
    have loc : (pre ++ crossed).length = request.insertion := by simpa only [List.length_append] using dest
    refine ⟨chosen, ?_, ?_, ?_⟩
    · rw [oldOrder, ← index, getAtPrefix]
    · unfold relocate
      rw [oldOrder, ← index, ← loc, eraseAtPrefix, ← List.append_assoc, insertAtPrefix]
      exact newOrder
    · rw [oldOrder]
      simp only [List.length_append, List.length_cons]
      omega

private theorem step?_spec (accepted : step? state request = some next) :
    ∃ origin, state.origins[request.binding]? = some origin ∧ origin ∉ state.moved ∧
      Header.Pair.move? state.cfg request = some next.cfg ∧
      next.origins = relocate request origin state.origins ∧ next.moved = origin :: state.moved := by
  obtain ⟨origin, found, emitted⟩ := Option.bind_eq_some_iff.mp accepted
  by_cases repeated : origin ∈ state.moved
  · simp [repeated] at emitted
  · simp only [ite_eq_right repeated] at emitted
    obtain ⟨cfg, moved, same⟩ := Option.bind_eq_some_iff.mp emitted
    cases same
    exact ⟨origin, found, repeated, moved, rfl, rfl⟩

private theorem relocate_perm {α : Type} {xs : List α} {chosen : α}
    (found : xs[request.binding]? = some chosen) (insertion : request.insertion < xs.length) :
    (relocate request chosen xs).Perm xs := by
  obtain ⟨source, value⟩ := List.getElem?_eq_some_iff.mp found
  have inBounds : request.insertion ≤ (xs.eraseIdx request.binding).length := by
    rw [List.length_eraseIdx_of_lt source]
    omega
  unfold relocate
  apply (List.perm_insertIdx chosen _ inBounds).trans
  rw [← value]
  exact List.getElem_cons_eraseIdx_perm source

private theorem map_relocate {α β : Type} (f : α → β) (chosen : α) (xs : List α) :
    (relocate request chosen xs).map f = relocate request (f chosen) (xs.map f) := by
  simp only [relocate, List.map_insertIdx, List.eraseIdx_map]

theorem initial_tracked (cfg : Cfg TargetOp (SourceLabel carried result) Input [result]) :
    Tracked (operations (cfg.block .header)) (initial cfg) := by
  let source := operations (cfg.block .header)
  refine ⟨List.Perm.refl _, ?_, List.nodup_nil⟩
  change (List.range source.length).map (fun i => source[i]?) = source.map some
  apply List.ext_getElem?
  intro i
  simp only [List.getElem?_map]
  by_cases within : i < source.length
  · simp only [List.getElem?_range within, Option.map_some, List.getElem?_eq_getElem within]
  · rw [List.getElem?_eq_none (by simpa using Nat.le_of_not_gt within),
      List.getElem?_eq_none (Nat.le_of_not_gt within)]
    rfl

theorem step?_tracked {source : List Operation} (tracked : Tracked source state)
    (accepted : step? state request = some next) : Tracked source next := by
  obtain ⟨origin, found, fresh, moved, origins, history⟩ := step?_spec accepted
  obtain ⟨chosen, atSource, changeOrder, inBounds⟩ := move?_transport moved
  have sameLength : state.origins.length = (operations (state.cfg.block .header)).length := by
    simpa only [List.length_map] using congrArg List.length tracked.2.1
  have originOp : source[origin]? = some chosen := by
    have atIndex := congrArg (fun seq : List (Option Operation) => seq[request.binding]?) tracked.2.1
    simpa only [List.getElem?_map, found, atSource, Option.map_some, Option.some.injEq] using atIndex
  refine ⟨?_, ?_, ?_⟩
  · rw [origins]
    exact (relocate_perm found (sameLength ▸ inBounds)).trans tracked.1
  · rw [origins, map_relocate, tracked.2.1, originOp, changeOrder, map_relocate]
  · rw [history, List.nodup_cons]
    exact ⟨fresh, tracked.2.2⟩

theorem run?_tracked {source : List Operation} (tracked : Tracked source state)
    (accepted : run? state requests = some next) : Tracked source next := by
  induction requests generalizing state with
  | nil => cases accepted; exact tracked
  | cons _ _ ih =>
    obtain ⟨_, first, rest⟩ := Option.bind_eq_some_iff.mp accepted
    exact ih (step?_tracked tracked first) rest

theorem run?_append (state : State Input carried result) (pre post : List Request) :
    run? state (pre ++ post) = (run? state pre).bind (fun next => run? next post) := by
  induction pre generalizing state with
  | nil => rfl
  | cons request pre ih => simp only [List.cons_append, run?, Option.bind_assoc, ih]

theorem schedule?_refuses_suffix {pre post : List Request}
    (ran : run? (initial (lower g)) pre = some state) (rejected : run? state post = none) :
    schedule? g (pre ++ post) = none := by
  simp [schedule?, run?_append, ran, rejected]

private theorem withHeader_self (cfg : Cfg TargetOp (SourceLabel carried result) Input [result]) :
    withHeader cfg (cfg.block .header) = cfg := by
  cases cfg
  simp only [withHeader]
  congr
  funext _ label
  cases label <;> rfl

theorem run?_header (accepted : run? state requests = some next) :
    ∃ header, next.cfg = withHeader state.cfg header ∧
      ∀ env, header.eval evalOp (fun term vals => term.eval vals) env =
        (state.cfg.block .header).eval evalOp (fun term vals => term.eval vals) env := by
  induction requests generalizing state with
  | nil =>
    cases accepted
    exact ⟨_, (withHeader_self _).symm, fun _ => rfl⟩
  | cons _ _ ih =>
    obtain ⟨middle, first, rest⟩ := Option.bind_eq_some_iff.mp accepted
    obtain ⟨_, _, _, moved, _, _⟩ := step?_spec first
    obtain ⟨_, midCfg, firstAgrees⟩ := Header.Pair.move?_header moved
    obtain ⟨header, lastCfg, restAgrees⟩ := ih rest
    refine ⟨header, ?_, ?_⟩
    · rw [lastCfg, midCfg]
      rfl
    · intro env
      rw [midCfg] at restAgrees
      exact (restAgrees env).trans (firstAgrees env)

private theorem schedule?_header (accepted : schedule? g requests = some out) :
    ∃ header, out = withHeader (lower g) header ∧
      ∀ env, header.eval evalOp (fun term vals => term.eval vals) env =
        ((lower g).block .header).eval evalOp (fun term vals => term.eval vals) env := by
  obtain ⟨_, ran, rfl⟩ := Option.map_eq_some_iff.mp accepted
  exact run?_header ran

theorem schedule?_frames (accepted : schedule? g requests = some out) (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) := by
  obtain ⟨_, rfl, agrees⟩ := schedule?_header accepted
  exact withHeader_frames agrees input

theorem schedule?_run_eq (accepted : schedule? g requests = some out) (input : Env Input)
    (fuel : Nat) : out.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨_, rfl, agrees⟩ := schedule?_header accepted
  exact withHeader_run_eq agrees input fuel

theorem schedule?_budget (accepted : schedule? g requests = some out) (input : Env Input)
    (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (schedule?_run_eq accepted input _).trans (lower_run g input budget)

theorem schedule?_denotePart (accepted : schedule? g requests = some out) (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input := by
  obtain ⟨_, rfl, agrees⟩ := schedule?_header accepted
  exact withHeader_denotePart agrees input

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence
