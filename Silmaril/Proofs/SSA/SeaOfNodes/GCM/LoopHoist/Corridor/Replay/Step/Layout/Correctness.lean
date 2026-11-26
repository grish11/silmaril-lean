module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Insert.Thms
import Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Thms
import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Thms

public section

namespace Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Cfg Terminator)
open Silmaril.SSA.SeaOfNodes
open Silmaril.SSA.SeaOfNodes.GCM
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout
open AfterReorder.Second (Candidate checkPrefixCut findCaptured?)
open AfterReorder.Second.Emit (emitAt?_entry liftCode liftCode_eval liftCode_targets_congr)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (Program TargetOp evalOp model lower_run)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : State Input saved carried result extra} {request : Nomination} {moved : Move state}

theorem initial?_spec {reference : Step.State Input saved carried result extra}
    (accepted : initial? reference = some state) : state.reference = reference ∧ Invariant state := by
  obtain ⟨⟨leading, tail⟩, split, out⟩ := Option.bind_eq_some_iff.mp accepted
  cases out
  have same := Saved.splitPrefix?_wrap split
  refine ⟨rfl, rfl, ⟨leading, tail, split, by intros; rfl⟩, ?_, ?_⟩
  · change (shape.ofBlock (leading.wrap tail)).target = (shape.ofBlock reference.cfg.entry).target
    rw [same]
  · intro input
    change (leading.wrap tail).eval evalOp _ input = _
    rw [same]

theorem savedCount_eq (valid : Invariant state) : state.savedCount = (extra ++ [saved]).length := by
  rw [State.savedCount, valid.scopeSize, List.length_append]
  simp

theorem emit?_spec (accepted : emit? state request = some moved) :
    Step.emit state.reference { request with cut := (extra ++ [saved]).length } = .ok moved.append ∧
    checkPrefixCut state.cfg (state.atLayout moved.append.candidate) request.cut = true ∧
    state.leading.insert? moved.append.candidate.op (state.savedCount - request.cut)
      (state.physicalOperands moved.append.candidate) = some moved.splice := by
  simp only [emit?] at accepted
  split at accepted
  next appended produced =>
    split at accepted
    next checked =>
      obtain ⟨splice, inserted, result⟩ := Option.bind_eq_some_iff.mp accepted
      cases result
      exact ⟨produced, checked, inserted⟩
    next => cases accepted
  next => cases accepted

theorem emit?_placement (accepted : emit? state request = some moved) :
    state.reference.origins[moved.append.index]? = some request.origin ∧
    findCaptured? moved.append.index 0 (Saved.origins (extra ++ [saved]))
      (state.cfg.block .header) = some moved.append.candidate ∧
    Legal state.cfg (state.atLayout moved.append.candidate).operands moved.append.candidate.uses ⟨none, request.cut⟩ ∧
    moved.splice.inserted.index = state.savedCount - request.cut := by
  obtain ⟨appended, checked, inserted⟩ := emit?_spec accepted
  obtain ⟨_, located, found, _, _, _, _⟩ := Step.emit_spec appended
  exact ⟨located, found, AfterReorder.Second.checkPrefixCut_legal checked, (Saved.Prefix.insert?_indices inserted).1⟩

theorem emit?_indices (accepted : emit? state request = some moved) :
    (moved.next.toPhysical .here).index = state.savedCount - request.cut ∧
    ∀ {w} (ref : Var ((extra ++ [saved]) ++ Input) w),
      let old := (state.toPhysical ref).index
      (moved.next.toPhysical (.there ref)).index =
        if old < state.savedCount - request.cut then old else old + 1 := by
  obtain ⟨_, _, inserted⟩ := emit?_spec accepted
  exact ⟨(Saved.Prefix.insert?_indices inserted).1,
    fun ref => (Saved.Prefix.insert?_indices inserted).2 (state.toPhysical ref)⟩

theorem emit?_physicalSlot (accepted : emit? state request = some moved) (origin : Nat) :
    moved.next.physicalSlot? origin =
      if origin = request.origin then some (state.savedCount - request.cut)
      else (state.physicalSlot? origin).map fun old =>
        if old < state.savedCount - request.cut then old else old + 1 := by
  obtain ⟨_, _, _, _, _, _, slots⟩ := Step.emit_spec (emit?_spec accepted).1
  obtain ⟨newIndex, shift⟩ := emit?_indices accepted
  unfold State.physicalSlot?
  change ((moved.append.next.slots.find? origin).map _) = _
  rw [slots]
  by_cases same : origin = request.origin
  · subst origin
    simp only [Saved.Slots.find?, BEq.refl]
    exact congrArg some newIndex
  · simp only [Saved.Slots.find?, beq_iff_eq, same]
    cases found : state.reference.slots.find? origin with
    | none => rfl
    | some tagged =>
      rcases tagged with ⟨width, ref⟩
      exact congrArg some (shift (Saved.prefixRef Input ref))

theorem physicalOperands_eval (valid : Invariant state) (input : Env Input) :
    ∃ leading tail,
      Saved.splitPrefix? state.reference.cfg.entry (extra ++ [saved]) = some (leading, tail) ∧
      ∀ candidate : Candidate Input saved carried result extra,
        (state.physicalOperands candidate).eval (state.leading.eval input) = candidate.inputs.eval (leading.eval input) := by
  obtain ⟨leading, tail, split, reads⟩ := valid.prefixAgreement
  exact ⟨leading, tail, split, fun candidate => evalRenameOperands state.toPhysical _ _ (reads input) candidate.inputs⟩

theorem emit?_invariant (valid : Invariant state) (accepted : emit? state request = some moved) :
    Invariant moved.next := by
  obtain ⟨appended, _, inserted⟩ := emit?_spec accepted
  obtain ⟨leading, tail, split, agree⟩ := valid.prefixAgreement
  have emitted := (Step.emit_spec appended).2.2.2.2.1
  have entryCode := emitAt?_entry split emitted
  have reads (input : Env Input) :=
    evalRenameOperands state.toPhysical _ _ (agree input) moved.append.candidate.inputs
  refine ⟨?_, ?_, ?_, ?_⟩
  · change moved.splice.physical.length = _
    rw [Saved.Prefix.insert?_length inserted, valid.scopeSize]
    rfl
  · refine ⟨.snoc leading moved.append.candidate.op moved.append.candidate.inputs, liftCode Var.there .here tail, ?_, ?_⟩
    · change Saved.splitPrefix? moved.append.next.cfg.entry _ = _
      rw [entryCode]
      exact Saved.splitPrefix?_snoc split _ _ _
    · intro input width ref
      cases ref with
      | here =>
        have value := Saved.Prefix.insert?_eval inserted input .here
        change (moved.splice.leading.eval input).get moved.splice.inserted = _
        exact value.trans (congrArg (evalOp moved.append.candidate.op) (reads input))
      | there ref =>
        exact (Saved.Prefix.insert?_eval inserted input (.there (state.toPhysical ref))).trans (agree input ref)
  · have targets := valid.targets
    change (shape.ofBlock (state.leading.wrap state.tail)).target = (shape.ofBlock state.reference.cfg.entry).target at targets
    rw [← Saved.splitPrefix?_wrap split, Saved.Prefix.wrap_targets, Saved.Prefix.wrap_targets] at targets
    change (shape.ofBlock (moved.splice.leading.wrap (liftCode moved.splice.previous moved.splice.inserted state.tail))).target =
      (shape.ofBlock moved.append.next.cfg.entry).target
    rw [entryCode, Saved.Prefix.wrap_targets, Saved.Prefix.wrap_targets]
    exact liftCode_targets_congr state.tail tail moved.splice.previous moved.splice.inserted Var.there .here targets
  · intro input
    let old := state.leading.eval input
    let physical := moved.splice.leading.eval input
    let value := evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (leading.eval input))
    have same {w : Width} (ref : Var _ w) := Saved.Prefix.insert?_eval inserted input ref
    have kept : physical.get moved.splice.inserted = value :=
      (same .here).trans (congrArg (evalOp moved.append.candidate.op) (reads input))
    have oldReads : ∀ {w} (ref : Var _ w), physical.get (moved.splice.previous ref) = old.get ref :=
      fun ref => same (.there ref)
    calc
      _ = (state.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input).map
          (Saved.prependFrame value) id := by
        change (moved.splice.leading.wrap (liftCode moved.splice.previous moved.splice.inserted state.tail)).eval
          evalOp (fun term env => Terminator.eval env term) input = _
        rw [Saved.Prefix.wrap_eval, liftCode_eval _ _ _ _ _ oldReads, kept]
        change _ = ((state.leading.wrap state.tail).eval evalOp
          (fun term env => Terminator.eval env term) input).map (Saved.prependFrame value) id
        rw [Saved.Prefix.wrap_eval]
      _ = _ := by
        change _ = moved.append.next.cfg.entry.eval evalOp _ input
        rw [valid.entry input, ← Saved.splitPrefix?_wrap split, entryCode, Saved.Prefix.wrap_eval, Saved.Prefix.wrap_eval]
        exact (liftCode_eval tail Var.there .here (leading.eval input) (.cons value (leading.eval input))
          (fun _ => rfl)).symm

theorem emit?_routes (valid : Invariant state) (accepted : emit? state request = some moved)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    Saved.StepRoutes state.cfg moved.next.cfg input values
      (evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (values.append input))) := by
  obtain ⟨_, _, found, _, emitted, _, _⟩ := Step.emit_spec (emit?_spec accepted).1
  have packet := (AfterReorder.Second.Emit.emitAt?_step matched found emitted).1
  refine ⟨?_, packet.block⟩
  rw [(emit?_invariant valid accepted).entry input, valid.entry input]
  exact packet.entry

theorem run_spec {position : Nat} {requests : List Nomination} {out : Output Input saved carried result}
    (valid : Invariant state) (accepted : run state position requests = .ok out) :
    Invariant out.2 ∧
      Step.run state.reference position (appendPlan (extra ++ [saved]).length requests) = .ok ⟨out.1, out.2.reference⟩ := by
  induction requests generalizing extra position with
  | nil =>
    cases accepted
    exact ⟨valid, rfl⟩
  | cons request rest ih =>
    cases found : emit? state request with
    | none => simp [Step.Layout.run, found] at accepted
    | some moved =>
      have continued : run moved.next (position + 1) rest = .ok out := by
        simpa only [Step.Layout.run, found] using accepted
      obtain ⟨invariant, reference⟩ := ih (emit?_invariant valid found) continued
      exact ⟨invariant, by
        simpa only [appendPlan, Step.run, (emit?_spec found).1, Move.next, List.cons_append, List.length_cons]
          using reference⟩

theorem state_run_eq (valid : Invariant state) (input : Env Input) (fuel : Nat) :
    state.cfg.run evalOp fuel input = state.reference.cfg.run evalOp fuel input :=
  Step.Earlier.run_eq_of_entry _ _ input fuel (valid.entry input) (fun _ => rfl)

theorem run_packets
    {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {inventory : List Nat} {input : Env Input} {values : Env (extra ++ [saved])}
    {position : Nat} {requests : List Nomination} {out : Output Input saved carried result}
    (valid : Invariant state)
    (prior : Saved.Invariant base state.reference.cfg inventory state.reference.origins state.reference.slots input values)
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values)
    (accepted : run state position requests = .ok out) :
    ∃ finalValues : Env (out.1 ++ [saved]),
      Saved.Invariant base out.2.cfg inventory out.2.reference.origins out.2.reference.slots input finalValues ∧
      Saved.Prefix.Matches out.2.reference.cfg.entry input finalValues := by
  obtain ⟨final, trace⟩ := run_spec valid accepted
  obtain ⟨finalValues, ref, matchedFinal, _⟩ := Step.run_invariant prior matched trace
  exact ⟨finalValues, ⟨ref.partition, ⟨(final.entry input).trans ref.routes.entry, ref.routes.block⟩⟩, matchedFinal⟩

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem state_denotePart (valid : Invariant state) (input : Env Input) :
    (Cfg.embed state.cfg).denotePart evalOp input = (Cfg.embed state.reference.cfg).denotePart evalOp input := by
  apply Part.ext
  intro value
  simp only [Cfg.mem_denotePart_iff, Cfg.embed_run, state_run_eq valid]

theorem run_fromTwo_budget {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    {g : Program Input carried result entrySigs headerSigs}
    {header : List Header.Pair.Request} {record : First Input carried result} {producer consumer : Nomination}
    {two : AfterReorder.Second.Emit.Emission Input carried result}
    {state : State Input two.prepared.intermediate.1 carried result [two.prepared.consumer.width]}
    {requests : List Nomination} {out : Output Input two.prepared.intermediate.1 carried result}
    (seed : replay g header [producer, consumer] = .ok (.two record consumer two))
    (initialized : initial? (Step.fromTwo record consumer two) = some state)
    (accepted : run state 2 requests = .ok out) (input : Env Input) (budget : Nat) :
    out.2.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) := by
  obtain ⟨same, valid⟩ := initial?_spec initialized
  obtain ⟨final, trace⟩ := run_spec valid accepted
  rw [same] at trace
  exact (state_run_eq final input _).trans
    ((Step.fromTwo_run_eq seed trace input _).trans (lower_run g input budget))

end Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout
