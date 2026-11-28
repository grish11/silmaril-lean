module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Thms
import Silmaril.SSA.SeaOfNodes.GCM.Dominance.Placement.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (Operands)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step
open AfterReorder.Second (checkConsumer findCaptured? findCaptured?_immutable findCaptured?_value valueAt?)
open AfterReorder.Second.Emit (emitAt? emitAt?_step)
open Loop.MLIR.CF (Program TargetOp evalOp lower lower_run model)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : State Input saved carried result extra} {request : Nomination}
variable {moved : Emission Input saved carried result extra}

theorem emit_spec (accepted : Step.emit state request = .ok moved) :
    request.cut = (extra ++ [saved]).length ∧
    state.origins[moved.index]? = some request.origin ∧
    findCaptured? moved.index 0 (Saved.origins (extra ++ [saved])) (state.cfg.block .header) =
      some moved.candidate ∧ checkConsumer state.cfg moved.candidate = true ∧
    emitAt? state.cfg moved.index moved.candidate.op moved.candidate.inputs = some moved.next.cfg ∧
    moved.next.origins = state.origins.eraseIdx moved.index ∧ moved.next.slots = .cons request.origin state.slots := by
  by_cases valid : request.cut = extra.length + 1
  · cases located : state.origins.idxOf? request.origin with
    | none => simp [Step.emit, valid, located] at accepted
    | some index =>
      cases found : findCaptured? index 0 (Saved.origins (extra ++ [saved])) (state.cfg.block .header) with
      | none => simp [Step.emit, valid, located, found] at accepted
      | some candidate =>
        cases check : checkConsumer state.cfg candidate with
        | false => simp [Step.emit, valid, located, found, check] at accepted
        | true =>
          cases edited : emitAt? state.cfg index candidate.op candidate.inputs with
          | none => simp [Step.emit, valid, located, found, check, edited] at accepted
          | some cfg =>
            simp [Step.emit, valid, located, found, check, edited] at accepted
            subst moved
            obtain ⟨bound, eq, _⟩ := List.idxOf?_eq_some_iff.mp located
            exact ⟨by simpa using valid, List.getElem?_eq_some_iff.mpr ⟨bound, eq⟩, found, check, edited, rfl, rfl⟩
  · simp [Step.emit, valid] at accepted

theorem emit_legal (accepted : Step.emit state request = .ok moved) :
    Legal state.cfg moved.candidate.operands moved.candidate.uses ⟨none, request.cut⟩ := by
  obtain ⟨cut, _, _, checked, _⟩ := emit_spec accepted
  rw [cut]
  exact AfterReorder.Second.checkPrefixCut_legal checked

theorem emit_header_value (accepted : Step.emit state request = .ok moved)
    (input : Env Input) (values : Env (extra ++ [saved])) (latch : BitVec carried.val) :
    valueAt? moved.index (state.cfg.block .header) ((values.append (.cons latch .nil)).append input) =
      some ⟨moved.candidate.width, evalOp moved.candidate.op (moved.candidate.inputs.eval (values.append input))⟩ :=
  findCaptured?_value (emit_spec accepted).2.2.1 _ _ (Saved.origins_agree values latch input)

theorem emit_immutable (accepted : Step.emit state request = .ok moved)
    {inputs : Operands Input moved.candidate.args} (immutable : moved.candidate.immutableInputs? = some inputs) :
    Legal state.cfg moved.candidate.operands moved.candidate.uses ⟨none, request.cut⟩ ∧
    (∀ operand ∈ moved.candidate.operands, operand = ⟨none, 0⟩) ∧
    ∀ (input : Env Input) (values : Env (extra ++ [saved])) (latch : BitVec carried.val),
      valueAt? moved.index (state.cfg.block .header) ((values.append (.cons latch .nil)).append input) =
        some ⟨moved.candidate.width, evalOp moved.candidate.op (inputs.eval input)⟩ := by
  obtain ⟨sites, evaluates⟩ := findCaptured?_immutable (emit_spec accepted).2.2.1 immutable
  refine ⟨emit_legal accepted, sites, fun input values latch => ?_⟩
  rw [emit_header_value accepted input values latch, evaluates input values]

theorem emit_of_saved_capture {index : Nat}
    {candidate : AfterReorder.Second.Candidate Input saved carried result extra}
    {target : Cfg TargetOp (Label saved carried result (candidate.width :: extra)) Input [result]}
    (cut : request.cut = (extra ++ [saved]).length) (located : state.origins.idxOf? request.origin = some index)
    (found : AfterReorder.Second.findCandidate? index 0 (Saved.origins (extra ++ [saved]))
      (state.cfg.block .header) = some candidate)
    (checked : checkConsumer state.cfg candidate = true)
    (edited : emitAt? state.cfg index candidate.op candidate.inputs = some target) :
    Step.emit state request = .ok ⟨index, candidate, ⟨target, state.origins.eraseIdx index,
      .cons request.origin state.slots⟩⟩ := by
  have coordinate : request.cut = extra.length + 1 := by simpa using cut
  simp [Step.emit, coordinate, located, AfterReorder.Second.findCandidate?_capture found, checked, edited]

theorem emit_invariant
    {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {inventory : List Nat} {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : Saved.Invariant base state.cfg inventory state.origins state.slots input values)
    (matched : Saved.Prefix.Matches state.cfg.entry input values)
    (accepted : Step.emit state request = .ok moved) :
    let value := evalOp moved.candidate.op (moved.candidate.inputs.eval (values.append input))
    Saved.Invariant base moved.next.cfg inventory moved.next.origins moved.next.slots input (.cons value values) ∧
    Saved.Prefix.Matches moved.next.cfg.entry input (.cons value values) ∧
    ∀ fuel, moved.next.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input := by
  obtain ⟨_, atIndex, found, _, emitted, origins, slots⟩ := emit_spec accepted
  obtain ⟨routes, entry⟩ := emitAt?_step matched found emitted
  refine ⟨?_, entry, Saved.extend_run_eq prior.routes routes⟩
  rw [origins, slots]
  exact prior.extend atIndex routes

theorem run_invariant
    {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {inventory : List Nat} {input : Env Input} {values : Env (extra ++ [saved])}
    {position : Nat} {requests : List Nomination} {out : Step.Output Input saved carried result}
    (prior : Saved.Invariant base state.cfg inventory state.origins state.slots input values)
    (matched : Saved.Prefix.Matches state.cfg.entry input values)
    (accepted : Step.run state position requests = .ok out) :
    ∃ values : Env (out.1 ++ [saved]),
      Saved.Invariant base out.2.cfg inventory out.2.origins out.2.slots input values ∧
      Saved.Prefix.Matches out.2.cfg.entry input values ∧
      ∀ fuel, out.2.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input := by
  induction requests generalizing extra position with
  | nil =>
    cases accepted
    exact ⟨values, prior, matched, fun _ => rfl⟩
  | cons request rest ih =>
    cases edited : Step.emit state request with
    | error reason => simp [Step.run, edited] at accepted
    | ok moved =>
      obtain ⟨extended, entry, equal⟩ := emit_invariant prior matched edited
      have success : Step.run moved.next (position + 1) rest = .ok out := by
        simpa only [Step.run, edited] using accepted
      obtain ⟨values, preserved, matched, final⟩ := ih extended entry success
      exact ⟨values, preserved, matched, fun fuel => (final fuel).trans (equal fuel)⟩

theorem run_refuses_at {position : Nat} {pre post : List Nomination}
    {after : Step.Output Input saved carried result} {reason : Reason}
    (prefixRan : Step.run state position pre = .ok after)
    (refused : Step.emit after.2 request = .error reason) :
    Step.run state position (pre ++ request :: post) =
      .error (.nomination (position + pre.length) request reason) := by
  induction pre generalizing extra position with
  | nil =>
    cases prefixRan
    simp [Step.run, refused]
  | cons prior pre ih =>
    cases edited : Step.emit state prior with
    | error reason => simp [Step.run, edited] at prefixRan
    | ok moved =>
      have ran : Step.run moved.next (position + 1) pre = .ok after := by
        simpa only [Step.run, edited] using prefixRan
      simpa [Step.run, edited, List.length_cons, Nat.add_left_comm, Nat.add_comm] using ih ran

variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {header : List Header.Pair.Request} {first : First Input carried result}
variable {producer consumer : Nomination}
variable {two : AfterReorder.Second.Emit.Emission Input carried result}

theorem fromTwo_invariant
    (accepted : replay g header [producer, consumer] = .ok (.two first consumer two)) (input : Env Input) :
    ∃ (base : Cfg TargetOp (SourceLabel carried result) Input [result]) (values : Env
        [two.prepared.consumer.width, two.prepared.intermediate.1]),
      let state := fromTwo first consumer two
      Saved.Invariant base state.cfg (List.range (Header.Earlier.operations ((lower g).block .header)).length)
        state.origins state.slots input values ∧ Saved.Prefix.Matches state.cfg.entry input values := by
  obtain ⟨before, _, _, _, _, _, _, prior, step, entry⟩ :=
    AfterReorder.Second.Emit.replay?_prefix_routes (replay_two_eq accepted) input
  exact ⟨before.cfg, _, ⟨replay_partition accepted, Saved.extend_routes prior step⟩, entry⟩

theorem fromTwo_run_eq {requests : List Nomination}
    (accepted : replay g header [producer, consumer] = .ok (.two first consumer two))
    {out : Step.Output Input two.prepared.intermediate.1 carried result}
    (continued : Step.run (fromTwo first consumer two) 2 requests = .ok out)
    (input : Env Input) (fuel : Nat) :
    out.2.cfg.run evalOp fuel input = (lower g).run evalOp fuel input := by
  obtain ⟨_, _, prior, matched⟩ := fromTwo_invariant accepted input
  obtain ⟨_, _, _, agreement⟩ := run_invariant prior matched continued
  exact (agreement fuel).trans (replay_run_eq accepted input fuel)

theorem replayAll_run_eq {nominations : List Nomination} {out : Step.Result Input carried result}
    (accepted : replayAll g header nominations = .ok out) (input : Env Input) (fuel : Nat) :
    out.cfg.run evalOp fuel input = (lower g).run evalOp fuel input := by
  have initial (requests : List Nomination)
      (ran : (Replay.replay g header requests).map Step.Result.initial = .ok out) :
      out.cfg.run evalOp fuel input = (lower g).run evalOp fuel input := by
    cases step : Replay.replay g header requests with
    | error reason => simp [Except.map, step] at ran
    | ok snapshot =>
      simp [Except.map, step] at ran
      subst out
      exact replay_run_eq step input fuel
  rcases nominations with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · exact initial [] accepted
  · exact initial [a] accepted
  · exact initial [a, b] accepted
  · cases seed : Replay.replay g header [a, b] with
    | error reason => simp [replayAll, seed] at accepted
    | ok snapshot =>
      cases snapshot with
      | zero state => simp [replayAll, seed] at accepted
      | one first => simp [replayAll, seed] at accepted
      | two first second moved =>
        have named : second = b := by
          obtain ⟨_, _, trace⟩ := replay_trace seed
          cases trace
          rfl
        subst second
        cases finished : Step.run (fromTwo first b moved) 2 (c :: rest) with
        | error reason => simp [replayAll, seed, finished, Except.map] at accepted
        | ok output =>
          simp [replayAll, seed, finished, Except.map] at accepted
          subst out
          exact fromTwo_run_eq seed finished input fuel

theorem replayAll_budget {nominations : List Nomination} {out : Step.Result Input carried result}
    (accepted : replayAll g header nominations = .ok out) (input : Env Input) (budget : Nat) :
    out.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  (replayAll_run_eq accepted input _).trans (lower_run g input budget)

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem replayAll_denotePart {nominations : List Nomination} {out : Step.Result Input carried result}
    (accepted : replayAll g header nominations = .ok out) (input : Env Input) :
    (Cfg.embed out.cfg).denotePart evalOp input = (Cfg.embed (lower g)).denotePart evalOp input := by
  apply Part.ext
  intro value
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, replayAll_run_eq accepted]

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step
