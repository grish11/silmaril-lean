module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Cfg)
open AfterReorder.Second (Candidate checkPrefixCut findCaptured?)
open Loop.MLIR.CF (Program TargetOp evalOp model)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : State Input saved carried result extra} {request : Nomination} {moved : Move state}

theorem initial?_spec {reference : Step.State Input saved carried result extra}
    (accepted : initial? reference = some state) : state.reference = reference ∧ Invariant state :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.initial?_spec accepted

theorem savedCount_eq (valid : Invariant state) : state.savedCount = (extra ++ [saved]).length :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.savedCount_eq valid

/-- The recorded append, physical cut check and typed splice are the ones
    that produced the next state. -/
theorem emit?_spec (accepted : emit? state request = some moved) :
    Step.emit state.reference { request with cut := (extra ++ [saved]).length } = .ok moved.append ∧
    checkPrefixCut state.cfg (state.atLayout moved.append.candidate) request.cut = true ∧
    state.leading.insert? moved.append.candidate.op (state.savedCount - request.cut)
      (state.physicalOperands moved.append.candidate) = some moved.splice :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.emit?_spec accepted

/-- Resolve the original identity in the actual current header and certify
    placement against the physical definitions and exact use occurrences. -/
theorem emit?_placement (accepted : emit? state request = some moved) :
    state.reference.origins[moved.append.index]? = some request.origin ∧
    findCaptured? moved.append.index 0 (Saved.origins (extra ++ [saved]))
      (state.cfg.block .header) = some moved.append.candidate ∧
    Legal state.cfg (state.atLayout moved.append.candidate).operands moved.append.candidate.uses ⟨none, request.cut⟩ ∧
    moved.splice.inserted.index = state.savedCount - request.cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.emit?_placement accepted

/-- Reading the updated map gives the exact new physical slot and shifts
    previous references only at or past the inserted definition. -/
theorem emit?_indices (accepted : emit? state request = some moved) :
    (moved.next.toPhysical .here).index = state.savedCount - request.cut ∧
    ∀ {w} (ref : Var ((extra ++ [saved]) ++ Input) w),
      let old := (state.toPhysical ref).index
      (moved.next.toPhysical (.there ref)).index =
        if old < state.savedCount - request.cut then old else old + 1 :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.emit?_indices accepted

/-- Original identities keep their references through the layout update. -/
theorem emit?_physicalSlot (accepted : emit? state request = some moved) (origin : Nat) :
    moved.next.physicalSlot? origin =
      if origin = request.origin then some (state.savedCount - request.cut)
      else (state.physicalSlot? origin).map fun old =>
        if old < state.savedCount - request.cut then old else old + 1 :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.emit?_physicalSlot accepted origin

theorem physicalOperands_eval (valid : Invariant state) (input : Env Input) :
    ∃ leading tail,
      Saved.splitPrefix? state.reference.cfg.entry (extra ++ [saved]) = some (leading, tail) ∧
      ∀ candidate : Candidate Input saved carried result extra,
        (state.physicalOperands candidate).eval (state.leading.eval input) = candidate.inputs.eval (leading.eval input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.physicalOperands_eval valid input

/-- Each successful insertion preserves the typed readings, successor
    slots and exact entry transfer relative to its new append reference. -/
theorem emit?_invariant (valid : Invariant state) (accepted : emit? state request = some moved) :
    Invariant moved.next :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.emit?_invariant valid accepted

theorem State.block_eq (state : State Input saved carried result extra) {args : List Width}
    (label : Label saved carried result extra args) : state.cfg.block label = state.reference.cfg.block label := rfl

/-- Both entry and feedback add the selected saved value to the logical
    packet. The exact exit transfer is retained. -/
theorem emit?_routes (valid : Invariant state) (accepted : emit? state request = some moved)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches state.reference.cfg.entry input values) :
    Saved.StepRoutes state.cfg moved.next.cfg input values
      (evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (values.append input))) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.emit?_routes valid accepted matched

/-- Every successful finite list preserves the invariant and identifies
    the exact reference produced by checked append replay. -/
theorem run_spec {position : Nat} {requests : List Nomination} {out : Output Input saved carried result}
    (valid : Invariant state) (accepted : run state position requests = .ok out) :
    Invariant out.2 ∧
      Step.run state.reference position (appendPlan (extra ++ [saved]).length requests) = .ok ⟨out.1, out.2.reference⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.run_spec valid accepted

theorem state_run_eq (valid : Invariant state) (input : Env Input) (fuel : Nat) :
    state.cfg.run evalOp fuel input = state.reference.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.state_run_eq valid input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem state_denotePart (valid : Invariant state) (input : Env Input) :
    (Cfg.embed state.cfg).denotePart evalOp input = (Cfg.embed state.reference.cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.state_denotePart valid input

/-- The emitted CFG carries the complete logical packets of the certified
    base at the end of any successful plan. -/
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
      Saved.Prefix.Matches out.2.reference.cfg.entry input finalValues :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.run_packets valid prior matched accepted

/-- A checked two-save seed relates block fuel to native backedge budget
    with the existing three-block offset. -/
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
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.run_fromTwo_budget seed initialized accepted input budget

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout
