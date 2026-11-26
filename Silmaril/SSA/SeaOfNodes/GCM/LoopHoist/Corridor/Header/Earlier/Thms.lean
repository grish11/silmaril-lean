module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg Frame)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input Γ : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {index : Nat} {cut : Point (SourceLabel carried result)}
variable {cfg out : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {before after : Block TargetOp (SourceLabel carried result) Γ [result]}

/-- A successful adjacent swap exchanges exactly two operation symbols. -/
theorem swapAt?_order {target : Nat} (swapped : swapAt? target before = some after) :
    ∃ (prefixOps : List Operation) (left right : Operation) (suffixOps : List Operation),
      prefixOps.length = target ∧
      operations before = prefixOps ++ (left :: right :: suffixOps) ∧
      operations after = prefixOps ++ (right :: left :: suffixOps) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.swapAt?_order swapped

/-- Every successful sequence of swaps removes the nominated operation from
after the crossed sequence and reinserts it ahead of that sequence. -/
theorem moveEarlier?_order {target extraSteps : Nat}
    (moved : moveEarlier? target extraSteps before = some after) :
    ∃ (prefixOps crossed : List Operation) (chosen : Operation) (suffixOps : List Operation),
      prefixOps.length = target ∧ crossed.length = extraSteps + 1 ∧
      operations before = prefixOps ++ crossed ++ (chosen :: suffixOps) ∧
      operations after = prefixOps ++ (chosen :: (crossed ++ suffixOps)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.moveEarlier?_order moved

/-- The composition preserves exact successor frames and returns. -/
theorem moveEarlier?_eval {target extraSteps : Nat}
    (moved : moveEarlier? target extraSteps before = some after) (env : Env Γ) :
    after.eval evalOp (fun term vals => term.eval vals) env =
      before.eval evalOp (fun term vals => term.eval vals) env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.moveEarlier?_eval moved env

/-- An earlier move replaces only the header and preserves its evaluated frame. -/
theorem moveAt?_header (moved : moveAt? cfg index cut = some out) :
    ∃ header, out = withHeader cfg header ∧
      ∀ env, header.eval evalOp (fun term vals => term.eval vals) env =
        (cfg.block .header).eval evalOp (fun term vals => term.eval vals) env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.moveAt?_header moved

/-- A one-position destination gives the existing adjacent emitter's result. -/
theorem moveAt?_adjacent (adjacent : afterRemoval index cut.cut + 1 = index) :
    moveAt? cfg index cut = Header.moveAt? cfg index cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.moveAt?_adjacent adjacent

/-- The returned cut is earlier in the original header and is the
synthesized legal placement for the original nominated binding. -/
theorem pickAndMove?_placement (picked : pickAndMove? g index = some (cut, out)) :
    cut.block = headerId ∧ cut.cut < index ∧ afterRemoval index cut.cut = cut.cut ∧
    cut ∈ candidateCuts (lower g) blocks ∧
    ∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩ ∧
      chooseCut? g binding.operands binding.uses = some cut ∧
      Legal (lower g) binding.operands binding.uses cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.pickAndMove?_placement picked

/-- The emitted CFG has the selected operation at the chosen original cut,
and all other operation symbols retain their relative order. -/
theorem pickAndMove?_order (picked : pickAndMove? g index = some (cut, out)) :
    ∃ (prefixOps crossed : List Operation) (chosen : Operation) (suffixOps : List Operation),
      prefixOps.length = cut.cut ∧ crossed.length = index - cut.cut ∧
      operations ((lower g).block .header) = prefixOps ++ crossed ++ (chosen :: suffixOps) ∧
      operations (out.block .header) = prefixOps ++ (chosen :: (crossed ++ suffixOps)) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.pickAndMove?_order picked

/-- Entry syntax and exact feedback, exit and return arguments agree. -/
theorem pickAndMove?_frames (picked : pickAndMove? g index = some (cut, out)) (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.pickAndMove?_frames picked input

theorem pickAndMove?_run_eq (picked : pickAndMove? g index = some (cut, out)) (input : Env Input)
    (fuel : Nat) : out.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.pickAndMove?_run_eq picked input fuel

theorem pickAndMove?_budget (picked : pickAndMove? g index = some (cut, out)) (input : Env Input)
    (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.pickAndMove?_budget picked input budget

theorem pickAndMove?_denotePart (picked : pickAndMove? g index = some (cut, out)) (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier.pickAndMove?_denotePart picked input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier
