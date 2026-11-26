module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later

open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Block Cfg Frame)
open Earlier (Operation operations)
open Loop.MLIR.CF (Program TargetOp evalOp lower model)

variable {Input Γ : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Program Input carried result entrySigs headerSigs}
variable {index : Nat} {cut : Point (SourceLabel carried result)}
variable {cfg out : Cfg TargetOp (SourceLabel carried result) Input [result]}
variable {before after : Block TargetOp (SourceLabel carried result) Γ [result]}

/-- The checked swaps preserve exact successor frames and returns. -/
theorem moveLater?_eval {extraSteps : Nat} (moved : moveLater? index extraSteps before = some after)
    (env : Env Γ) : after.eval evalOp (fun term vals => term.eval vals) env =
      before.eval evalOp (fun term vals => term.eval vals) env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.moveLater?_eval moved env

/-- The checker validates the binding found at the current index. -/
theorem checkBindingCut_sound (checked : checkBindingCut cfg index cut = true) :
    ∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins (cfg.block .header) = some ⟨saved, binding⟩ ∧
      Legal cfg binding.operands binding.uses cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.checkBindingCut_sound checked

theorem moveCfgAt?_checked (moved : moveCfgAt? cfg index cut = some out) :
    checkBindingCut cfg index cut = true :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.moveCfgAt?_checked moved

/-- A later move replaces only the header and preserves its evaluated frame. -/
theorem moveCfgAt?_header (moved : moveCfgAt? cfg index cut = some out) :
    ∃ header, out = withHeader cfg header ∧
      ∀ env, header.eval evalOp (fun term vals => term.eval vals) env =
        (cfg.block .header).eval evalOp (fun term vals => term.eval vals) env :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.moveCfgAt?_header moved

/-- A checked later cut is legal for the located source binding. Its
post-removal insertion index is one less than the original cut. -/
theorem checkDestination_sound (checked : checkDestination g index cut = true) :
    cut.block = headerId ∧ index + 1 < cut.cut ∧ afterRemoval index cut.cut = cut.cut - 1 ∧
    ∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩ ∧
      Legal (lower g) binding.operands binding.uses cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.checkDestination_sound checked

theorem moveAt?_placement (moved : moveAt? g index cut = some out) :
    cut.block = headerId ∧ index + 1 < cut.cut ∧ afterRemoval index cut.cut = cut.cut - 1 ∧
    ∃ (saved : Width) (binding : Binding Input (carried :: Input) saved carried result),
      findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩ ∧
      Legal (lower g) binding.operands binding.uses cut :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.moveAt?_placement moved

/-- A same-block read before the proposed original cut prevents emission. -/
theorem moveAt?_refuses_lateUse {saved : Width}
    {binding : Binding Input (carried :: Input) saved carried result}
    (found : findBinding index 0 headerOrigins ((lower g).block .header) = some ⟨saved, binding⟩)
    {use : Use (SourceLabel carried result)} {read : Point (SourceLabel carried result)}
    (member : use ∈ binding.uses) (resolved : use.point? (lower g) = some read)
    (sameBlock : cut.block = read.block) (passed : read.cut < cut.cut) :
    moveAt? g index cut = none :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.moveAt?_refuses_lateUse
    found member resolved sameBlock passed

/-- The nominated operation appears at the translated insertion index.
Every crossed operation retains its relative order. -/
theorem moveAt?_order (moved : moveAt? g index cut = some out) :
    ∃ (prefixOps crossed : List Operation) (chosen : Operation) (suffixOps : List Operation),
      prefixOps.length = index ∧ prefixOps.length + crossed.length = cut.cut - 1 ∧
      operations ((lower g).block .header) = prefixOps ++ (chosen :: (crossed ++ suffixOps)) ∧
      operations (out.block .header) = prefixOps ++ crossed ++ (chosen :: suffixOps) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.moveAt?_order moved

/-- Entry syntax and the complete feedback, exit and return tuples agree. -/
theorem moveAt?_frames (moved : moveAt? g index cut = some out) (input : Env Input) :
    out.entry = (lower g).entry ∧
    ∀ frame : Frame (SourceLabel carried result),
      (out.block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) =
        ((lower g).block frame.label).eval evalOp (fun term env => term.eval env) (frame.args.append input) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.moveAt?_frames moved input

theorem moveAt?_run_eq (moved : moveAt? g index cut = some out) (input : Env Input)
    (fuel : Nat) : out.run evalOp fuel input = (lower g).run evalOp fuel input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.moveAt?_run_eq moved input fuel

theorem moveAt?_budget (moved : moveAt? g index cut = some out) (input : Env Input) (budget : Nat) :
    out.run evalOp (budget + 3) input =
      (g.evalBackedges model budget (Silmaril.SSA.SeaOfNodes.MLIR.sourceInputs input)).map
        (fun value => Env.cons value .nil) :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.moveAt?_budget moved input budget

theorem moveAt?_denotePart (moved : moveAt? g index cut = some out) (input : Env Input) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed out).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (lower g)).denotePart evalOp input :=
  Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later.moveAt?_denotePart moved input

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Later
