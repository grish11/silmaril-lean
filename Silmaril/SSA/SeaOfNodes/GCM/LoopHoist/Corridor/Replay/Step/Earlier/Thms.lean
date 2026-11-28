module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Thms
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Insert.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier

open Silmaril.MLIR.Arith (Env Var Width)
open Silmaril.MLIR.CF (Cfg Terminator)
open AfterReorder.Second (checkPrefixCut)
open Loop.MLIR.CF (Program TargetOp evalOp model)

variable {Input extra : List Width} {saved carried result : Width}
variable {state : Step.State Input saved carried result extra} {request : Nomination}
variable {moved : Emission Input saved carried result extra}

/-- Successful emission uses the nominated cut and an actual split of
    the current entry. The append witness resolves the same original identity. -/
theorem emit?_spec (accepted : emit? state request = some moved) :
    request.cut < (extra ++ [saved]).length ∧
    Step.emit state { request with cut := (extra ++ [saved]).length } = .ok moved.append ∧
    checkPrefixCut state.cfg moved.append.candidate request.cut = true ∧
    ∃ leading, Saved.splitPrefix? state.cfg.entry (extra ++ [saved]) = some (leading, moved.tail) ∧
      leading.insert? moved.append.candidate.op ((extra ++ [saved]).length - request.cut)
        moved.append.candidate.inputs = some moved.splice :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.emit?_spec accepted

/-- The earlier cut is legal for the exact reads, and the new definition
    is followed by exactly the old lets after that cut in the saved prefix. -/
theorem emit?_placement (accepted : emit? state request = some moved) :
    moved.append.candidate.operandCut? request.cut = true ∧
      Legal state.cfg moved.append.candidate.operands moved.append.candidate.uses ⟨none, request.cut⟩ ∧
      moved.splice.inserted.index = (extra ++ [saved]).length - request.cut := by
  obtain ⟨_, _, checked, _, _, inserted⟩ := emit?_spec accepted
  exact ⟨(Bool.and_eq_true_iff.mp checked).1, AfterReorder.Second.checkPrefixCut_legal checked,
    (Saved.Prefix.insert?_indices inserted).1⟩

/-- The entry keeps the exact successor slots of the append CFG. All
    labeled blocks, including both header terminator arms, are shared. -/
theorem emit?_entry_targets (accepted : emit? state request = some moved) :
    (shape moved.cfg none).target = (shape moved.append.next.cfg none).target :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.emit?_entry_targets accepted

theorem Emission.block_eq (moved : Emission Input saved carried result extra) :
    ∀ {args} (label : Label saved carried result (moved.append.candidate.width :: extra) args),
      moved.cfg.block label = moved.append.next.cfg.block label := fun _ => rfl

/-- Entry computes the same logical packet as append for every input. -/
theorem emit?_entry_eq (accepted : emit? state request = some moved) (input : Env Input) :
    moved.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input =
      moved.append.next.cfg.entry.eval evalOp (fun term env => Terminator.eval env term) input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.emit?_entry_eq accepted input

/-- The physical map reads the logical environment of the actual append prefix. -/
theorem emit?_prefix_agree (accepted : emit? state request = some moved) :
    ∃ leading tail,
      Saved.splitPrefix? moved.append.next.cfg.entry ((moved.append.candidate.width :: extra) ++ [saved]) =
        some (leading, tail) ∧
      ∀ (input : Env Input) {w} (ref : Var _ w),
        (moved.splice.leading.eval input).get (moved.splice.toPhysical ref) = (leading.eval input).get ref :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.emit?_prefix_agree accepted

theorem run_eq_of_entry {Labels : List Width → Type}
    (left right : Cfg TargetOp Labels Input [result]) (input : Env Input) (fuel : Nat)
    (entry : left.entry.eval evalOp (fun term env => Terminator.eval env term) input =
      right.entry.eval evalOp (fun term env => Terminator.eval env term) input)
    (blocks : ∀ {args} (label : Labels args), left.block label = right.block label) :
    left.run evalOp fuel input = right.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.run_eq_of_entry left right input fuel entry blocks

/-- On the current prefix values, entry and feedback prepend the same
    saved word to the old packet. The exact exit payload is preserved. -/
theorem emit?_routes (accepted : emit? state request = some moved)
    {input : Env Input} {values : Env (extra ++ [saved])}
    (matched : Saved.Prefix.Matches state.cfg.entry input values) :
    Saved.StepRoutes state.cfg moved.cfg input values
      (evalOp moved.append.candidate.op (moved.append.candidate.inputs.eval (values.append input))) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.emit?_routes accepted matched

/-- Both emitted CFGs agree on returns and exhaustion at every common block fuel. -/
theorem emit?_run_eq (accepted : emit? state request = some moved) (input : Env Input) (fuel : Nat) :
    moved.cfg.run evalOp fuel input = moved.append.next.cfg.run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.emit?_run_eq accepted input fuel

open Silmaril.MLIR.CF.SwitchAssert (Cfg) in
theorem emit?_denotePart (accepted : emit? state request = some moved) (input : Env Input) :
    (Cfg.embed moved.cfg).denotePart evalOp input =
      (Cfg.embed moved.append.next.cfg).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.emit?_denotePart accepted input

/-- Starting from the checked two-save seed, native backedge budget maps
    to CFG block fuel by the existing offset. -/
theorem emit?_fromTwo_budget {entrySigs headerSigs : List (List (Diamond.Ty Width))}
    {g : Program Input carried result entrySigs headerSigs}
    {header : List Header.Pair.Request} {first : First Input carried result} {producer consumer : Nomination}
    {two : AfterReorder.Second.Emit.Emission Input carried result}
    {moved : Emission Input two.prepared.intermediate.1 carried result [two.prepared.consumer.width]}
    (seed : replay g header [producer, consumer] = .ok (.two first consumer two))
    (accepted : emit? (Step.fromTwo first consumer two) request = some moved)
    (input : Env Input) (budget : Nat) :
    moved.cfg.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.emit?_fromTwo_budget seed accepted input budget

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier
