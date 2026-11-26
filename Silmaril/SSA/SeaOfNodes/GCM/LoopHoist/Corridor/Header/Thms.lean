module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg Frame)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input Γ : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {index : Nat} {cut : Point (SourceLabel carried result)}
variable {out : Cfg TargetOp (SourceLabel carried result) Input [result]}

/-- The local swap preserves the branch decision and the complete typed frame
or return value, for every header environment. -/
theorem swapAt?_eval {insertion : Nat}
    {before after : Block TargetOp (SourceLabel carried result) Γ [result]}
    (swapped : swapAt? insertion before = some after) (env : Env Γ) :
    after.eval evalOp (fun term vals => term.eval vals) env =
      before.eval evalOp (fun term vals => term.eval vals) env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.swapAt?_eval swapped env

/-- The emitted move uses the synthesized legal cut for the actual binding.
The adjacent earlier cut retains its index after removal. -/
theorem pickAndMove?_placement (picked : pickAndMove? g index = some (cut, out)) :
    cut.block = headerId ∧ cut.cut + 1 = index ∧ afterRemoval index cut.cut = cut.cut ∧
    cut ∈ candidateCuts (lower g) blocks ∧
    ∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩ ∧
      chooseCut? g binding.operands binding.uses = some cut ∧
      Legal (lower g) binding.operands binding.uses cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndMove?_placement picked

/-- A selected cut outside the supported adjacent earlier position is refused,
including either cut that reinserts the binding at its original index. -/
theorem pickAndMove?_refuses (outside : ¬ (cut.block = headerId ∧
    afterRemoval index cut.cut + 1 = index))
    {saved : Width} {binding : Binding Input (carried :: Input) saved carried result}
    (found : findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩)
    (selected : chooseCut? g binding.operands binding.uses = some cut) :
    pickAndMove? g index = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndMove?_refuses outside found selected

/-- The preheader agrees syntactically and each block agrees on its exact
successor frame or return. This includes feedback and exit arguments. -/
theorem pickAndMove?_frames (picked : pickAndMove? g index = some (cut, out)) (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndMove?_frames picked input

theorem pickAndMove?_run_eq (picked : pickAndMove? g index = some (cut, out))
    (input : Env Input) (fuel : Nat) :
    out.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndMove?_run_eq picked input fuel

theorem pickAndMove?_budget (picked : pickAndMove? g index = some (cut, out))
    (input : Env Input) (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndMove?_budget picked input budget

/-- Partial observations agree, including their domains of definition. -/
theorem pickAndMove?_denotePart (picked : pickAndMove? g index = some (cut, out)) (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.pickAndMove?_denotePart picked input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header
