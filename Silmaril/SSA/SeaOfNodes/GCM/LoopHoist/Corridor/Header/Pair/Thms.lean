module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Cfg Frame)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {cfg middle out : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {request first second : Request}

/-- Every successful step checked the binding and cut in its own input CFG. -/
theorem move?_checked (moved : move? cfg request = some out) :
    Later.checkBindingCut cfg request.binding request.point = true :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.move?_checked moved

/-- The second step runs on the emitted CFG and nominates a different binding. -/
theorem schedule?_steps (accepted : schedule? g first second = some out) :
    ∃ middle, move? (lower g) first = some middle ∧ second.binding ≠ first.insertion ∧
      move? middle second = some out :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.schedule?_steps accepted

/-- A rejected second request yields no rewritten CFG. -/
theorem schedule?_refuses_second (firstMove : move? (lower g) first = some middle)
    (secondRejected : move? middle second = none) : schedule? g first second = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.schedule?_refuses_second firstMove secondRejected

/-- Both exact successor tuples and the exit return agree with the input CFG. -/
theorem schedule?_frames (accepted : schedule? g first second = some out) (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.schedule?_frames accepted input

theorem schedule?_run_eq (accepted : schedule? g first second = some out) (input : Env Input)
    (fuel : Nat) : out.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.schedule?_run_eq accepted input fuel

theorem schedule?_budget (accepted : schedule? g first second = some out) (input : Env Input)
    (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.schedule?_budget accepted input budget

theorem schedule?_denotePart (accepted : schedule? g first second = some out) (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.schedule?_denotePart accepted input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair
