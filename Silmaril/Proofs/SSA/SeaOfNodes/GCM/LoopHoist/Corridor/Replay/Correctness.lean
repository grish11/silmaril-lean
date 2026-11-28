module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Mathlib.Data.List.InsertIdx
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF.SwitchAssert (Cfg)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Header.Earlier (operations)
open Header.Sequence (State)
open Loop.MLIR.CF (Program evalOp lower lower_run model)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {header : List Header.Pair.Request} {nominations : List Nomination}
variable {before : State Input carried result} {snapshot : Snapshot Input carried result}
variable {first : First Input carried result} {producer consumer : Nomination}
variable {moved : AfterReorder.Second.Emit.Emission Input carried result}

theorem run_append (state : Snapshot Input carried result) (position : Nat) (pre post : List Nomination) :
    run state position (pre ++ post) =
      (run state position pre).bind (fun after => run after (position + pre.length) post) := by
  induction pre generalizing state position with
  | nil => rfl
  | cons nomination pre ih =>
    cases step : advance state nomination with
    | error reason => simp [run, step, Except.bind]
    | ok next => simp [run, step, ih, List.length_cons, Nat.add_left_comm, Nat.add_comm]

theorem run_refuses_at {state next : Snapshot Input carried result} {position : Nat}
    {pre post : List Nomination} {nomination : Nomination} {reason : Reason}
    (prior : run state position pre = .ok next) (invalid : advance next nomination = .error reason) :
    run state position (pre ++ nomination :: post) =
      .error (.nomination (position + pre.length) nomination reason) := by
  rw [run_append, prior]
  simp [Except.bind, run, invalid]

private theorem run_trace {position : Nat}
    (accepted : run (.zero before) position nominations = .ok snapshot) :
    Trace before nominations snapshot := by
  cases nominations with
  | nil =>
    cases accepted
    exact .zero
  | cons producer rest =>
    cases firstStep : first? before producer with
    | error reason => simp [run, advance, Except.map, firstStep] at accepted
    | ok first =>
      cases rest with
      | nil =>
        simp [run, advance, Except.map, firstStep] at accepted
        subst snapshot
        exact .one firstStep
      | cons consumer rest =>
        cases secondStep : second? first consumer with
        | error reason => simp [run, advance, Except.map, firstStep, secondStep] at accepted
        | ok moved =>
          cases rest with
          | nil =>
            simp [run, advance, Except.map, firstStep, secondStep] at accepted
            subst snapshot
            exact .two firstStep secondStep
          | cons _ _ => simp [run, advance, Except.map, firstStep, secondStep] at accepted

theorem replay_trace (accepted : replay g header nominations = .ok snapshot) :
    ∃ before, Header.Sequence.run? (Header.Sequence.initial (lower g)) header = some before ∧
      Trace before nominations snapshot := by
  cases ran : Header.Sequence.run? (Header.Sequence.initial (lower g)) header with
  | none => simp [replay, ran] at accepted
  | some before =>
    refine ⟨before, rfl, run_trace (position := 0) ?_⟩
    simpa only [replay, ran] using accepted

theorem first?_spec (accepted : first? before producer = .ok first) :
    first.nomination = producer ∧ first.cut = ⟨none, 0⟩ ∧ producer.cut = 0 ∧
      before.origins[first.index]? = some producer.origin ∧
      first.origins = before.origins.eraseIdx first.index ∧
      AfterReorder.resolveMove? before producer.origin = some (first.index, first.cut, first.output) := by
  by_cases valid : producer.cut = 0
  · cases resolved : AfterReorder.resolveMove? before producer.origin with
    | none => simp [first?, valid, resolved] at accepted
    | some move =>
      rcases move with ⟨index, cut, output⟩
      simp [first?, valid, resolved] at accepted
      subst first
      obtain ⟨origin, emitted⟩ := AfterReorder.resolveMove?_spec resolved
      obtain ⟨_, _, _, site, _⟩ := hoistCodeWith?_spec emitted
      exact ⟨rfl, site, valid, Header.Priority.resolve?_sound origin, rfl, rfl⟩
  · simp [first?, valid] at accepted

theorem second?_spec (accepted : second? first consumer = .ok moved) :
    secondCut consumer moved = ⟨none, 1⟩ ∧
      AfterReorder.Second.prepareOn? first.output first.origins consumer.origin = some moved.prepared ∧
      AfterReorder.Second.Emit.emit? moved.prepared = some moved.cfg := by
  by_cases valid : consumer.cut = 1
  · cases checked : AfterReorder.Second.prepareOn? first.output first.origins consumer.origin with
    | none => simp [second?, valid, checked] at accepted
    | some prepared =>
      cases emitted : AfterReorder.Second.Emit.emit? prepared with
      | none => simp [second?, valid, checked, emitted] at accepted
      | some cfg =>
        simp [second?, valid, checked, emitted] at accepted
        subst moved
        exact ⟨by simp [secondCut, valid], rfl, emitted⟩
  · simp [second?, valid] at accepted

theorem second?_current (accepted : second? first consumer = .ok moved) :
    moved.prepared.intermediate = first.output ∧ moved.prepared.origins = first.origins ∧
      first.origins[moved.prepared.index]? = some consumer.origin := by
  obtain ⟨same, origins, located, _, _⟩ := AfterReorder.Second.prepareOn?_spec (second?_spec accepted).2.1
  obtain ⟨bound, eq, _⟩ := List.idxOf?_eq_some_iff.mp located
  refine ⟨same, origins, ?_⟩
  rw [← origins]
  exact List.getElem?_eq_some_iff.mpr ⟨bound, eq⟩

private theorem firstReplay
    (ran : Header.Sequence.run? (Header.Sequence.initial (lower g)) header = some before)
    (checked : first? before producer = .ok first) :
    AfterReorder.replay? g ⟨header, producer.origin⟩ = some first.output := by
  simp [AfterReorder.replay?, AfterReorder.finish?, ran, (first?_spec checked).2.2.2.2.2]

private theorem secondReplay
    (ran : Header.Sequence.run? (Header.Sequence.initial (lower g)) header = some before)
    (firstChecked : first? before producer = .ok first) (secondChecked : second? first consumer = .ok moved) :
    AfterReorder.Second.Emit.replay? g ⟨header, producer.origin⟩ consumer.origin = some moved := by
  obtain ⟨_, _, _, _, origins, firstResolved⟩ := first?_spec firstChecked
  obtain ⟨_, checked, emitted⟩ := second?_spec secondChecked
  have prepared : AfterReorder.Second.prepare? g ⟨header, producer.origin⟩ consumer.origin = some moved.prepared := by
    simpa [AfterReorder.Second.prepare?, ran, firstResolved, ← origins] using checked
  cases moved
  simp [AfterReorder.Second.Emit.replay?, prepared, emitted]

theorem replay_one_eq (accepted : replay g header [producer] = .ok (.one first)) :
    AfterReorder.replay? g ⟨header, producer.origin⟩ = some first.output := by
  obtain ⟨_, ran, trace⟩ := replay_trace accepted
  cases trace with
  | one checked => exact firstReplay ran checked

theorem replay_two_eq (accepted : replay g header [producer, consumer] = .ok (.two first consumer moved)) :
    AfterReorder.Second.Emit.replay? g ⟨header, producer.origin⟩ consumer.origin = some moved := by
  obtain ⟨_, ran, trace⟩ := replay_trace accepted
  cases trace with
  | two checked later => exact secondReplay ran checked later

theorem replay_two_complete
    (emitted : AfterReorder.Second.Emit.replay? g ⟨header, producer.origin⟩ consumer.origin = some moved)
    (firstCut : producer.cut = 0) (nextCut : consumer.cut = 1) :
    ∃ first, replay g header [producer, consumer] = .ok (.two first consumer moved) := by
  obtain ⟨prepared, checked, remaining⟩ := Option.bind_eq_some_iff.mp emitted
  obtain ⟨cfg, edited, eq⟩ := Option.bind_eq_some_iff.mp remaining
  change some (AfterReorder.Second.Emit.Emission.mk prepared cfg) = some moved at eq
  cases eq
  obtain ⟨before, ran, remaining⟩ := Option.bind_eq_some_iff.mp checked
  obtain ⟨⟨index, cut, output⟩, resolved, consumerChecked⟩ := Option.bind_eq_some_iff.mp remaining
  let first : First Input carried result := ⟨producer, index, cut, output, before.origins.eraseIdx index⟩
  have secondCheck : AfterReorder.Second.prepareOn? first.output first.origins consumer.origin = some prepared :=
    consumerChecked
  have moveFirst : first? before producer = .ok first := by
    simp [first?, firstCut, resolved, first]
  have moveSecond : second? first consumer = .ok ⟨prepared, cfg⟩ := by
    simp [second?, nextCut, secondCheck, edited]
  exact ⟨first, by simp [replay, ran, run, advance, Except.map, moveFirst, moveSecond]⟩

theorem replay_origins (accepted : replay g header nominations = .ok snapshot) :
    snapshot.origins.map (fun origin => (operations ((lower g).block .header))[origin]?) =
      snapshot.headerOperations.map some := by
  obtain ⟨before, ran, trace⟩ := replay_trace accepted
  have tracked := Header.Sequence.run?_tracked (Header.Sequence.initial_tracked (lower g)) ran
  cases trace with
  | zero => exact tracked.2.1
  | one checked =>
    obtain ⟨_, _, _, _, erased, resolved⟩ := first?_spec checked
    have order := AfterReorder.Second.hoistCodeWith?_operations (AfterReorder.resolveMove?_spec resolved).2
    simp only [Snapshot.origins, Snapshot.headerOperations]
    rw [erased, ← List.eraseIdx_map, tracked.2.1, List.eraseIdx_map, order]
  | two firstChecked secondChecked =>
    have exactReplay := secondReplay ran firstChecked secondChecked
    have prepared := (AfterReorder.Second.Emit.replay?_spec exactReplay).1
    obtain ⟨_, _, _, _, _, _, aligned, _⟩ := AfterReorder.Second.prepare?_placement prepared
    have order := AfterReorder.Second.Emit.replay?_header_operations exactReplay
    simp only [Snapshot.origins, Snapshot.headerOperations]
    rw [← List.eraseIdx_map, aligned, List.eraseIdx_map, order]

theorem replay_partition (accepted : replay g header nominations = .ok snapshot) :
    (snapshot.savedSlots.origins ++ snapshot.origins).Perm
      (List.range (operations ((lower g).block .header)).length) := by
  obtain ⟨before, ran, trace⟩ := replay_trace accepted
  have original := (Header.Sequence.run?_tracked (Header.Sequence.initial_tracked (lower g)) ran).1
  cases trace with
  | zero => exact original
  | one checked =>
    obtain ⟨named, _, _, located, erased, _⟩ := first?_spec checked
    simp only [Snapshot.savedSlots, Snapshot.origins, named, erased]
    exact (Saved.promote_perm (w := _) .nil located).trans original
  | two checked later =>
    obtain ⟨named, _, _, located, erased, _⟩ := first?_spec checked
    obtain ⟨_, remaining, current⟩ := second?_current later
    simp only [Snapshot.savedSlots, Snapshot.origins, named, remaining]
    exact (Saved.promote_perm (w := _) (.cons _ .nil) current).trans
      (erased ▸ (Saved.promote_perm (w := _) .nil located).trans original)

theorem locate?_header {origin index : Nat}
    (located : snapshot.locate? origin = some (.inl index)) :
    snapshot.origins[index]? = some origin := by
  cases found : snapshot.origins.idxOf? origin with
  | none => simp [Snapshot.locate?, found, Option.map_eq_some_iff] at located
  | some current =>
    simp [Snapshot.locate?, found] at located
    subst current
    obtain ⟨bound, eq, _⟩ := List.idxOf?_eq_some_iff.mp found
    exact List.getElem?_eq_some_iff.mpr ⟨bound, eq⟩

theorem locate?_saved {origin : Nat} {w : Width} {ref : Var snapshot.savedWidths w}
    (located : snapshot.locate? origin = some (.inr ⟨w, ref⟩)) :
    snapshot.savedSlots.origin ref = origin := by
  cases found : snapshot.origins.idxOf? origin with
  | some current => simp [Snapshot.locate?, found] at located
  | none =>
    simp only [Snapshot.locate?, found, Option.map_eq_some_iff] at located
    obtain ⟨slot, read, eq⟩ := located
    simp only [Sum.inr.injEq] at eq
    subst slot
    exact Saved.Slots.find?_origin read

theorem locate?_exists {origin : Nat} (accepted : replay g header nominations = .ok snapshot)
    (bound : origin < (operations ((lower g).block .header)).length) :
    ∃ loc, snapshot.locate? origin = some loc := by
  have present : origin ∈ snapshot.savedSlots.origins ++ snapshot.origins :=
    (replay_partition accepted).mem_iff.mpr (List.mem_range.mpr bound)
  cases found : snapshot.origins.idxOf? origin with
  | some current => exact ⟨.inl current, by simp [Snapshot.locate?, found]⟩
  | none =>
    have saved : origin ∈ snapshot.savedSlots.origins :=
      (List.mem_append.mp present).resolve_right (List.idxOf?_eq_none_iff.mp found)
    obtain ⟨slot, read⟩ := Saved.Slots.find?_exists saved
    exact ⟨.inr slot, by simp [Snapshot.locate?, found, read]⟩

theorem replay_two_invariant (accepted : replay g header [producer, consumer] = .ok (.two first consumer moved))
    (input : Env Input) :
    ∃ state : State Input carried result,
      Header.Sequence.run? (Header.Sequence.initial (lower g)) header = some state ∧
      ∃ (firstValue : BitVec moved.prepared.intermediate.1.val),
        let inventory := List.range (operations ((lower g).block .header)).length
        let secondValue := evalOp moved.prepared.consumer.op (moved.prepared.consumer.inputs.eval (.cons firstValue input))
        Saved.Invariant state.cfg moved.prepared.intermediate.2 inventory first.origins
          (.cons first.nomination.origin .nil) input (.cons firstValue .nil) ∧
        Saved.Invariant state.cfg moved.cfg inventory (.two first consumer moved : Snapshot Input carried result).origins
          (.two first consumer moved : Snapshot Input carried result).savedSlots
          input (.cons secondValue (.cons firstValue .nil)) := by
  obtain ⟨before, ranBefore, trace⟩ := replay_trace accepted
  obtain ⟨state, _, _, _, _, ran, _, prior, step⟩ :=
    AfterReorder.Second.Emit.replay?_packet_step (replay_two_eq accepted) input
  rw [ran] at ranBefore
  have same := Option.some.inj ranBefore
  subst before
  cases trace with
  | two firstChecked secondChecked =>
    obtain ⟨named, _, _, selected, erased, _⟩ := first?_spec firstChecked
    obtain ⟨_, remaining, current⟩ := second?_current secondChecked
    have original := (Header.Sequence.run?_tracked (Header.Sequence.initial_tracked (lower g)) ran).1
    have partition : ((Saved.Slots.cons (w := moved.prepared.intermediate.1) first.nomination.origin .nil).origins ++
        first.origins).Perm (List.range (operations ((lower g).block .header)).length) := by
      rw [named, erased]
      exact (Saved.promote_perm (w := _) .nil selected).trans original
    refine ⟨state, ran, _, ⟨partition, prior⟩, ?_⟩
    simp only [Snapshot.origins, Snapshot.savedSlots, remaining]
    exact Saved.Invariant.extend ⟨partition, prior⟩ current step

theorem replay_run_eq (accepted : replay g header nominations = .ok snapshot)
    (input : Env Input) (fuel : Nat) :
    snapshot.cfg.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨before, ran, trace⟩ := replay_trace accepted
  cases trace with
  | zero =>
    have scheduled : Header.Sequence.schedule? g header = some before.cfg := by
      simp [Header.Sequence.schedule?, ran]
    exact Header.Sequence.schedule?_run_eq scheduled input fuel
  | one checked => exact AfterReorder.replay?_run_eq (firstReplay ran checked) input fuel
  | two firstChecked secondChecked =>
    have exactReplay := secondReplay ran firstChecked secondChecked
    exact (AfterReorder.Second.Emit.replay?_run_eq exactReplay input fuel).trans
      (AfterReorder.replay?_run_eq (AfterReorder.Second.Emit.replay?_spec exactReplay).2.2 input fuel)

theorem replay_denotePart (accepted : replay g header nominations = .ok snapshot) (input : Env Input) :
    (Cfg.embed snapshot.cfg).denotePart evalOp input = (Cfg.embed (lower g)).denotePart evalOp input := by
  apply Part.ext
  intro outcome
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, replay_run_eq accepted]

theorem replay_budget (accepted : replay g header nominations = .ok snapshot) (input : Env Input) (budget : Nat) :
    snapshot.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (replay_run_eq accepted input _).trans (lower_run g input budget)

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
