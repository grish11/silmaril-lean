module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg)
open Silmaril.MLIR.Pure (Operands)
open AfterReorder.Second (checkConsumer findCaptured? valueAt?)
open AfterReorder.Second.Emit (emitAt?)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : State Input saved carried result extra} {request : Nomination}
variable {moved : Emission Input saved carried result extra}

/-- Successful checking uses the actual selected cut, binding and emitted CFG. -/
theorem emit_spec (accepted : emit state request = .ok moved) :
    request.cut = (extra ++ [saved]).length ∧
    state.origins[moved.index]? = some request.origin ∧
    findCaptured? moved.index 0 (Saved.origins (extra ++ [saved])) (state.cfg.block .header) =
      some moved.candidate ∧ checkConsumer state.cfg moved.candidate = true ∧
    emitAt? state.cfg moved.index moved.candidate.op moved.candidate.inputs = some moved.next.cfg ∧
    moved.next.origins = state.origins.eraseIdx moved.index ∧ moved.next.slots = .cons request.origin state.slots :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.emit_spec accepted

/-- The identified placement is legal on the current typed CFG. -/
theorem emit_legal (accepted : emit state request = .ok moved) :
    Legal state.cfg moved.candidate.operands moved.candidate.uses ⟨none, request.cut⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.emit_legal accepted

/-- On the actual current header the selected binding has the same value
for every latch argument with the given saved values and immutable inputs. -/
theorem emit_header_value (accepted : emit state request = .ok moved)
    (input : Env Input) (values : Env (extra ++ [saved])) (latch : BitVec carried.val) :
    valueAt? moved.index (state.cfg.block .header) ((values.append (.cons latch .nil)).append input) =
      some ⟨moved.candidate.width, evalOp moved.candidate.op (moved.candidate.inputs.eval (values.append input))⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.emit_header_value accepted input values latch

/-- The append cut is legal, immutable operands come from cut zero, and
the value on the actual header depends only on those inputs. -/
theorem emit_immutable (accepted : emit state request = .ok moved)
    {inputs : Operands Input moved.candidate.args} (immutable : moved.candidate.immutableInputs? = some inputs) :
    Legal state.cfg moved.candidate.operands moved.candidate.uses ⟨none, request.cut⟩ ∧
    (∀ operand ∈ moved.candidate.operands, operand = ⟨none, 0⟩) ∧
    ∀ (input : Env Input) (values : Env (extra ++ [saved])) (latch : BitVec carried.val),
      valueAt? moved.index (state.cfg.block .header) ((values.append (.cons latch .nil)).append input) =
        some ⟨moved.candidate.width, evalOp moved.candidate.op (inputs.eval input)⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.emit_immutable accepted immutable

/-- A successful prior saved-dependent check gives exactly the same
candidate, CFG, and origin update under the enriched emitter. -/
theorem emit_of_saved_capture {index : Nat}
    {candidate : AfterReorder.Second.Candidate Input saved carried result extra}
    {target : Cfg TargetOp (Label saved carried result (candidate.width :: extra)) Input [result]}
    (cut : request.cut = (extra ++ [saved]).length) (located : state.origins.idxOf? request.origin = some index)
    (found : AfterReorder.Second.findCandidate? index 0 (Saved.origins (extra ++ [saved]))
      (state.cfg.block .header) = some candidate)
    (checked : checkConsumer state.cfg candidate = true)
    (edited : emitAt? state.cfg index candidate.op candidate.inputs = some target) :
    emit state request = .ok ⟨index, candidate, ⟨target, state.origins.eraseIdx index,
      .cons request.origin state.slots⟩⟩ :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.emit_of_saved_capture cut located found checked edited

/-- The checked step extends both the typed packet and its entry-prefix witness. -/
theorem emit_invariant
    {base : Cfg TargetOp (SourceLabel carried result) Input [result]}
    {inventory : List Nat} {input : Env Input} {values : Env (extra ++ [saved])}
    (prior : Saved.Invariant base state.cfg inventory state.origins state.slots input values)
    (matched : Saved.Prefix.Matches state.cfg.entry input values)
    (accepted : emit state request = .ok moved) :
    let value := evalOp moved.candidate.op (moved.candidate.inputs.eval (values.append input))
    Saved.Invariant base moved.next.cfg inventory moved.next.origins moved.next.slots input (.cons value values) ∧
    Saved.Prefix.Matches moved.next.cfg.entry input (.cons value values) ∧
    ∀ fuel, moved.next.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.emit_invariant prior matched accepted

/-- A successful suffix preserves the packet invariant and every fuel observation. -/
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
      ∀ fuel, out.2.cfg.run evalOp fuel input = state.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.run_invariant prior matched accepted

/-- The first invalid nomination reports its exact position and returns no CFG. -/
theorem run_refuses_at {position : Nat} {pre post : List Nomination}
    {after : Step.Output Input saved carried result} {reason : Reason}
    (prefixRan : Step.run state position pre = .ok after)
    (refused : emit after.2 request = .error reason) :
    Step.run state position (pre ++ request :: post) =
      .error (.nomination (position + pre.length) request reason) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.run_refuses_at prefixRan refused

variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {header : List Header.Pair.Request} {first : First Input carried result}
variable {producer consumer : Nomination}
variable {two : AfterReorder.Second.Emit.Emission Input carried result}

/-- The exact two-hoist replay supplies the starting invariant and typed entry prefix. -/
theorem fromTwo_invariant
    (accepted : replay g header [producer, consumer] = .ok (.two first consumer two)) (input : Env Input) :
    ∃ (base : Cfg TargetOp (SourceLabel carried result) Input [result]) (values : Env
        [two.prepared.consumer.width, two.prepared.intermediate.1]),
      let state := fromTwo first consumer two
      Saved.Invariant base state.cfg (List.range (Header.Earlier.operations ((lower g).block .header)).length)
        state.origins state.slots input values ∧ Saved.Prefix.Matches state.cfg.entry input values :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.fromTwo_invariant accepted input

/-- The seeded continuation agrees with the original lowering at every CFG fuel. -/
theorem fromTwo_run_eq {requests : List Nomination}
    (accepted : replay g header [producer, consumer] = .ok (.two first consumer two))
    {out : Step.Output Input two.prepared.intermediate.1 carried result}
    (continued : Step.run (fromTwo first consumer two) 2 requests = .ok out)
    (input : Env Input) (fuel : Nat) :
    out.2.cfg.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.fromTwo_run_eq accepted continued input fuel

/-- All successful lists preserve returns and exhaustion at the original CFG fuel. -/
theorem replayAll_run_eq {nominations : List Nomination} {out : Step.Result Input carried result}
    (accepted : replayAll g header nominations = .ok out) (input : Env Input) (fuel : Nat) :
    out.cfg.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.replayAll_run_eq accepted input fuel

theorem replayAll_budget {nominations : List Nomination} {out : Step.Result Input carried result}
    (accepted : replayAll g header nominations = .ok out) (input : Env Input) (budget : Nat) :
    out.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.replayAll_budget accepted input budget

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem replayAll_denotePart {nominations : List Nomination} {out : Step.Result Input carried result}
    (accepted : replayAll g header nominations = .ok out) (input : Env Input) :
    (Cfg.embed out.cfg).denotePart evalOp input = (Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.replayAll_denotePart accepted input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step
