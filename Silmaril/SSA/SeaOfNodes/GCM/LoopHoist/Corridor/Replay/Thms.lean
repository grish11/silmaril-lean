module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF.SwitchAssert (Cfg)
open Header.Earlier (operations)
open Header.Sequence (State)
open Loop.MLIR.CF (Program evalOp lower model)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {header : List Header.Pair.Request} {nominations : List Nomination}
variable {before : State Input carried result} {snapshot : Snapshot Input carried result}
variable {first : First Input carried result} {producer consumer : Nomination}
variable {moved : AfterReorder.Second.Emit.Emission Input carried result}

/-- A successful prefix determines the current snapshot for the suffix. -/
theorem run_append (state : Snapshot Input carried result) (position : Nat) (pre post : List Nomination) :
    run state position (pre ++ post) =
      (run state position pre).bind (fun after => run after (position + pre.length) post) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.run_append state position pre post

/-- A failure at the next nomination reports its position and cannot return the prefix CFG. -/
theorem run_refuses_at {state next : Snapshot Input carried result} {position : Nat}
    {pre post : List Nomination} {nomination : Nomination} {reason : Reason}
    (prior : run state position pre = .ok next) (invalid : advance next nomination = .error reason) :
    run state position (pre ++ nomination :: post) =
      .error (.nomination (position + pre.length) nomination reason) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.run_refuses_at prior invalid

/-- The returned snapshot records exactly the checks that replay executed. -/
theorem replay_trace (accepted : replay g header nominations = .ok snapshot) :
    ∃ before, Header.Sequence.run? (Header.Sequence.initial (lower g)) header = some before ∧
      Trace before nominations snapshot :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.replay_trace accepted

/-- The first record retains the actual source cut, resolved binding and emitted CFG. -/
theorem first?_spec (accepted : first? before producer = .ok first) :
    first.nomination = producer ∧ first.cut = ⟨none, 0⟩ ∧ producer.cut = 0 ∧
      before.origins[first.index]? = some producer.origin ∧
      first.origins = before.origins.eraseIdx first.index ∧
      AfterReorder.resolveMove? before producer.origin = some (first.index, first.cut, first.output) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.first?_spec accepted

/-- The second decision consumes the stored first CFG and origin order. -/
theorem second?_spec (accepted : second? first consumer = .ok moved) :
    secondCut consumer moved = ⟨none, 1⟩ ∧
      AfterReorder.Second.prepareOn? first.output first.origins consumer.origin = some moved.prepared ∧
      AfterReorder.Second.Emit.emit? moved.prepared = some moved.cfg :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.second?_spec accepted

/-- The consumer was resolved in the first emission's actual header order. -/
theorem second?_current (accepted : second? first consumer = .ok moved) :
    moved.prepared.intermediate = first.output ∧ moved.prepared.origins = first.origins ∧
      first.origins[moved.prepared.index]? = some consumer.origin :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.second?_current accepted

theorem replay_one_eq (accepted : replay g header [producer] = .ok (.one first)) :
    AfterReorder.replay? g ⟨header, producer.origin⟩ = some first.output :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.replay_one_eq accepted

/-- The accepted two-step emission, including its typed CFG, is the existing
sequential emitter's exact result. -/
theorem replay_two_eq (accepted : replay g header [producer, consumer] = .ok (.two first consumer moved)) :
    AfterReorder.Second.Emit.replay? g ⟨header, producer.origin⟩ consumer.origin = some moved :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.replay_two_eq accepted

/-- Every prior two-step success replays to that same emission at cuts zero and one. -/
theorem replay_two_complete
    (emitted : AfterReorder.Second.Emit.replay? g ⟨header, producer.origin⟩ consumer.origin = some moved)
    (firstCut : producer.cut = 0) (nextCut : consumer.cut = 1) :
    ∃ first, replay g header [producer, consumer] = .ok (.two first consumer moved) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.replay_two_complete emitted firstCut nextCut

/-- The remaining original identities align with the typed emitted header order. -/
theorem replay_origins (accepted : replay g header nominations = .ok snapshot) :
    snapshot.origins.map (fun origin => (operations ((lower g).block .header))[origin]?) =
      snapshot.headerOperations.map some :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.replay_origins accepted

/-- Every original identity appears once in the saved prefix or surviving header. -/
theorem replay_partition (accepted : replay g header nominations = .ok snapshot) :
    (snapshot.savedSlots.origins ++ snapshot.origins).Perm
      (List.range (operations ((lower g).block .header)).length) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.replay_partition accepted

theorem locate?_header {origin index : Nat}
    (located : snapshot.locate? origin = some (.inl index)) :
    snapshot.origins[index]? = some origin :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.locate?_header located

theorem locate?_saved {origin : Nat} {w : Width} {ref : Var snapshot.savedWidths w}
    (located : snapshot.locate? origin = some (.inr ⟨w, ref⟩)) :
    snapshot.savedSlots.origin ref = origin :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.locate?_saved located

theorem locate?_exists {origin : Nat} (accepted : replay g header nominations = .ok snapshot)
    (bound : origin < (operations ((lower g).block .header)).length) :
    ∃ loc, snapshot.locate? origin = some loc :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.locate?_exists accepted bound

/-- Both emitted CFGs route their saved prefixes over the same reordered
CFG. The newer prefix extends the previous one by the consumer result. -/
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
          input (.cons secondValue (.cons firstValue .nil)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.replay_two_invariant accepted input

theorem replay_run_eq (accepted : replay g header nominations = .ok snapshot)
    (input : Env Input) (fuel : Nat) :
    snapshot.cfg.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.replay_run_eq accepted input fuel

theorem replay_budget (accepted : replay g header nominations = .ok snapshot) (input : Env Input) (budget : Nat) :
    snapshot.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.replay_budget accepted input budget

theorem replay_denotePart (accepted : replay g header nominations = .ok snapshot) (input : Env Input) :
    (Cfg.embed snapshot.cfg).denotePart evalOp input = (Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.replay_denotePart accepted input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay
