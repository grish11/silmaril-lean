module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Block Cfg Terminator)
open Silmaril.MLIR.Pure (Operands)
open Header.Earlier (operations)
open Header.Typed (edgePackets)
open Header.Sequence (State)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {first : AfterReorder.Plan} {consumerOrigin : Nat}
variable {prepared : Prepared Input carried result} {moved : Emission Input carried result}

/-- The typed rewrite keeps the branch choice, extends the selected header
packet and preserves all selected exit operands. -/
theorem liftTerm_eval {Γ Δ extra : List Width} {saved consumer : Width}
    (rename : Rename Γ Δ) (keep : Var Δ consumer)
    (term : Terminator (Label saved carried result extra) [result] Γ) (source : Env Γ) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref) :
    (liftTerm rename keep term).eval target =
      (term.eval source).map (Saved.prependFrame (target.get keep)) id :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.liftTerm_eval rename keep term source target same

/-- Remapping the entry tail and retaining a computed value extends exactly
    the header packets. Branch choices and exit packets are preserved. -/
theorem liftCode_eval {Γ Δ extra : List Width} {saved consumer : Width}
    (code : Block TargetOp (Label saved carried result extra) Γ [result])
    (rename : Rename Γ Δ) (keep : Var Δ consumer) (source : Env Γ) (target : Env Δ)
    (same : ∀ {w} (ref : Var Γ w), target.get (rename ref) = source.get ref) :
    (liftCode rename keep code).eval evalOp (fun term env => Terminator.eval env term) target =
      (code.eval evalOp (fun term env => Terminator.eval env term) source).map (Saved.prependFrame (target.get keep)) id :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.liftCode_eval code rename keep source target same

/-- Lifting saved arguments preserves the destination at each exact terminator slot. -/
theorem liftCode_target {Γ Δ extra : List Width} {saved consumer : Width}
    (code : Block TargetOp (Label saved carried result extra) Γ [result])
    (rename : Rename Γ Δ) (keep : Var Δ consumer) (slot : EdgeSlot) :
    (shape.ofBlock (liftCode rename keep code)).target slot =
      ((shape.ofBlock code).target slot).map liftTarget :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.liftCode_target code rename keep slot

/-- Extending the carried packet respects each terminator occurrence. -/
theorem liftCode_targets_congr {Γ Δ Γ' Δ' extra : List Width} {saved consumer : Width}
    (left : Block TargetOp (Label saved carried result extra) Γ [result])
    (right : Block TargetOp (Label saved carried result extra) Γ' [result])
    (rename : Rename Γ Δ) (keep : Var Δ consumer) (rename' : Rename Γ' Δ') (keep' : Var Δ' consumer)
    (same : (shape.ofBlock left).target = (shape.ofBlock right).target) :
    (shape.ofBlock (liftCode rename keep left)).target = (shape.ofBlock (liftCode rename' keep' right)).target :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.liftCode_targets_congr
    left right rename keep rename' keep' same

/-- The checked append CFG has the exact split prefix, new let and lifted tail. -/
theorem emitAt?_entry {args extra : List Width} {saved consumer : Width}
    {op : TargetOp args consumer} {operands : Operands ((extra ++ [saved]) ++ Input) args}
    {cfg : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {index : Nat} {target : Cfg TargetOp (Label saved carried result (consumer :: extra)) Input [result]}
    {leading : Saved.Prefix Input ((extra ++ [saved]) ++ Input)}
    {tail : Block TargetOp (Label saved carried result extra) ((extra ++ [saved]) ++ Input) [result]}
    (split : Saved.splitPrefix? cfg.entry (extra ++ [saved]) = some (leading, tail))
    (emitted : emitAt? cfg index op operands = some target) :
    target.entry = leading.wrap (.letOp op operands (liftCode Var.there .here tail)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.emitAt?_entry split emitted

/-- The shared splice preserves evaluated transfers and extends the checked
entry-prefix evaluation witness for the next step. -/
theorem emitAt?_step {saved : Width} {extra : List Width}
    {cfg : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {candidate : Candidate Input saved carried result extra} {index : Nat}
    {target : Cfg TargetOp (Label saved carried result (candidate.width :: extra)) Input [result]}
    {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches cfg.entry input values)
    (found : findCaptured? index 0 (Saved.origins (extra ++ [saved])) (cfg.block .header) = some candidate)
    (emitted : emitAt? cfg index candidate.op candidate.inputs = some target) :
    let value := evalOp candidate.op (candidate.inputs.eval (values.append input))
    Saved.StepRoutes cfg target input values value ∧
      Saved.Prefix.Matches target.entry input (.cons value values) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.emitAt?_step matched found emitted

/-- On the related header environments, every conditional occurrence
    transports its own argument packet, including the untaken edge. -/
theorem emitAt?_edgePackets {saved : Width} {extra : List Width}
    {cfg : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {candidate : Candidate Input saved carried result extra} {index : Nat}
    {target : Cfg TargetOp (Label saved carried result (candidate.width :: extra)) Input [result]}
    (found : findCaptured? index 0 (Saved.origins (extra ++ [saved])) (cfg.block .header) = some candidate)
    (emitted : emitAt? cfg index candidate.op candidate.inputs = some target)
    (input : Env Input) (values : Env (extra ++ [saved])) (latch : BitVec carried.val) :
    let value := evalOp candidate.op (candidate.inputs.eval (values.append input))
    let source := (values.append (.cons latch .nil)).append input
    (target.block .header).eval evalOp edgePackets (.cons value source) =
      ((cfg.block .header).eval evalOp edgePackets source).map
        (fun packet => (packet.1, Saved.prependFrame value packet.2)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.emitAt?_edgePackets
    found emitted input values latch

/-- Substitution and edge lifting preserve the order of every retained let. -/
theorem rewriteAt?_operations {Γ Δ extra : List Width} {saved consumer : Width}
    {code : Block TargetOp (Label saved carried result extra) Γ [result]}
    {index : Nat} {rename : Rename Γ Δ} {keep : Var Δ consumer}
    {out : Block TargetOp (Label saved carried result (consumer :: extra)) Δ [result]}
    (done : rewriteAt? index rename keep code = some out) :
    operations out = (operations code).eraseIdx index :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.rewriteAt?_operations done

/-- A shared splice removes the selected typed operation and keeps the
remaining header operations in order for every saved-prefix length. -/
theorem emitAt?_operations {args extra : List Width} {index : Nat} {saved consumer : Width}
    {cfg : Cfg TargetOp (Label saved carried result extra) Input [result]}
    {target : Cfg TargetOp (Label saved carried result (consumer :: extra)) Input [result]}
    {op : TargetOp args consumer} {operands : Operands ((extra ++ [saved]) ++ Input) args}
    (emitted : emitAt? cfg index op operands = some target) :
    operations (target.block .header) = (operations (cfg.block .header)).eraseIdx index :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.emitAt?_operations emitted

/-- Replay uses the checked handoff from the exact first emission and then
edits that CFG. -/
theorem replay?_spec (accepted : replay? g first consumerOrigin = some moved) :
    prepare? g first consumerOrigin = some moved.prepared ∧
      emit? moved.prepared = some moved.cfg ∧ AfterReorder.replay? g first = some moved.prepared.intermediate :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_spec accepted

/-- Every accepted handoff supplies the typed structure needed to emit. -/
theorem prepare?_emits (accepted : prepare? g first consumerOrigin = some prepared) :
    ∃ target, emit? prepared = some target :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.prepare?_emits accepted

/-- The old leading let is followed by the inserted consumer. The current
header is rewritten at the checked index. Transfers prepend the new
result to the prior header packet and preserve exit arguments exactly. -/
theorem replay?_routes (accepted : replay? g first consumerOrigin = some moved) (input : Env Input) :
    ∃ (args : List Width) (producer : TargetOp args moved.prepared.intermediate.1)
      (operands : Operands Input args) (tail : Block TargetOp (Label moved.prepared.intermediate.1 carried result)
        (moved.prepared.intermediate.1 :: Input) [result]),
      moved.prepared.intermediate.2.entry = .letOp producer operands tail ∧
      moved.cfg.entry = .letOp producer operands
        (.letOp moved.prepared.consumer.op moved.prepared.consumer.inputs (liftCode Var.there .here tail)) ∧
      rewriteAt? moved.prepared.index Var.there .here (moved.prepared.intermediate.2.block .header) =
        some (moved.cfg.block .header) ∧
      moved.cfg.block .exit = .terminator (.ret (.cons .here .nil)) ∧
      let saved := evalOp producer (operands.eval input)
      let value := evalOp moved.prepared.consumer.op (moved.prepared.consumer.inputs.eval (.cons saved input))
      StepRoutes moved.prepared.intermediate.2 moved.cfg input saved value :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_routes accepted input

/-- The second replay deletes the current index and retains the remaining operation order. -/
theorem replay?_header_operations (accepted : replay? g first consumerOrigin = some moved) :
    operations (moved.cfg.block .header) =
      (operations (moved.prepared.intermediate.2.block .header)).eraseIdx moved.prepared.index :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_header_operations accepted

/-- The actual first emission establishes the old packet invariant, and
the checked second edit is one instance of a typed packet extension. -/
theorem replay?_packet_step (accepted : replay? g first consumerOrigin = some moved) (input : Env Input) :
    ∃ (state : State Input carried result)
      (args : List Width) (producer : TargetOp args moved.prepared.intermediate.1)
      (operands : Operands Input args) (tail : Block TargetOp (Label moved.prepared.intermediate.1 carried result)
        (moved.prepared.intermediate.1 :: Input) [result]),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header = some state ∧
      moved.prepared.intermediate.2.entry = .letOp producer operands tail ∧
      let firstValue := evalOp producer (operands.eval input)
      let secondValue := evalOp moved.prepared.consumer.op (moved.prepared.consumer.inputs.eval (.cons firstValue input))
      RoutesWith state.cfg moved.prepared.intermediate.2 input (.cons firstValue .nil) ∧
      StepRoutes moved.prepared.intermediate.2 moved.cfg input firstValue secondValue :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_packet_step accepted input

/-- The actual two-save entry computes the same saved values used in the
edge simulation, so it supplies a starting prefix for another step. -/
theorem replay?_prefix_routes (accepted : replay? g first consumerOrigin = some moved) (input : Env Input) :
    ∃ (state : State Input carried result)
      (args : List Width) (producer : TargetOp args moved.prepared.intermediate.1)
      (operands : Operands Input args) (tail : Block TargetOp (Label moved.prepared.intermediate.1 carried result)
        (moved.prepared.intermediate.1 :: Input) [result]),
      Header.Sequence.run? (Header.Sequence.initial (lower g)) first.header = some state ∧
      moved.prepared.intermediate.2.entry = .letOp producer operands tail ∧
      let firstValue := evalOp producer (operands.eval input)
      let secondValue := evalOp moved.prepared.consumer.op (moved.prepared.consumer.inputs.eval (.cons firstValue input))
      RoutesWith state.cfg moved.prepared.intermediate.2 input (.cons firstValue .nil) ∧
      StepRoutes moved.prepared.intermediate.2 moved.cfg input firstValue secondValue ∧
      Saved.Prefix.Matches moved.cfg.entry input (.cons secondValue (.cons firstValue .nil)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_prefix_routes accepted input

/-- The second edit preserves both return and exhaustion at the same CFG fuel. -/
theorem replay?_run_eq (accepted : replay? g first consumerOrigin = some moved)
    (input : Env Input) (fuel : Nat) :
    moved.cfg.run evalOp fuel input = moved.prepared.intermediate.2.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_run_eq accepted input fuel

/-- Native budget plus the preheader, final header test and exit gives CFG fuel. -/
theorem replay?_budget (accepted : replay? g first consumerOrigin = some moved)
    (input : Env Input) (budget : Nat) :
    moved.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_budget accepted input budget

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
/-- The complete replay preserves the native lowering's partial denotation. -/
theorem replay?_denotePart (accepted : replay? g first consumerOrigin = some moved) (input : Env Input) :
    (Cfg.embed moved.cfg).denotePart evalOp input = (Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.replay?_denotePart accepted input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit
