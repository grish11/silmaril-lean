module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit.Defs
public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.DeleteExit.Correctness

/-! Typed syntax and exact execution laws for the one-exit cleanup. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit

open Diamond.SCCP (TupleCovers)
open PruneExit (InputFacts)
open SeaOfNodes.MLIR (sourceInputs)
open SeaOfNodes.MLIR.Lowering (lowerCode)
open Loop.MLIR.CF (entryScope evalOp model opcode)
open Loop.MLIR.CF.Bank (bankOperands headerScope lower)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF (Frame Terminator)
open Silmaril.MLIR.CF.SwitchAssert (Outcome)

variable {Γ carried : List Width} {result : Width}
variable {cfg : FullCfg Γ carried result} {clean : HeaderCfg Γ carried result}

/-- At the retained header, evaluation agrees after embedding its exact frame.
In particular the header argument values and order are preserved. -/
theorem header_eval (deleted : delete cfg = some clean) (env : Env (carried ++ Γ)) :
    (cfg.block .header).eval evalOp (fun term scope => Terminator.eval scope term) env =
      ((clean.block .header).eval evalOp (fun term scope => Terminator.eval scope term) env).map embedFrame id :=
  Proofs.restrictBlock_eval (Proofs.delete_blocks deleted).2 env

/-- The cleanup agrees from every retained header frame, at each block budget. -/
theorem runFrom_eq (deleted : delete cfg = some clean) (fuel : Nat) (input : Env Γ)
    (frame : Frame (HeaderLabel carried)) :
    clean.runFrom evalOp fuel input frame = cfg.runFrom evalOp fuel input (embedFrame frame) :=
  Proofs.runFrom_eq deleted fuel input frame

theorem run_eq (deleted : delete cfg = some clean) (fuel : Nat) (input : Env Γ) :
    clean.run evalOp fuel input = cfg.run evalOp fuel input :=
  Proofs.run_eq deleted fuel input

theorem denotePart_eq (deleted : delete cfg = some clean) (input : Env Γ) :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed clean).denotePart evalOp input =
      (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed cfg).denotePart evalOp input :=
  Proofs.denotePart_eq deleted input

variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}
variable {g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs} {facts : InputFacts Γ}

/-- The two surviving blocks use the original lowering and exact typed argument lists. -/
theorem delete_feedback (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) :
    delete (PruneInfeasibleExit.directFeedback g) =
      some { entry := lowerCode opcode g.preheader (entryScope Γ)
               (fun scope => .br ⟨.header, bankOperands scope (g.phiInputs .entry)⟩)
             block := fun
               | .header => lowerCode opcode g.header (headerScope Γ carried)
                   (fun scope => .br ⟨.header, bankOperands scope (g.phiInputs .backedge)⟩) } :=
  Proofs.delete_feedback g

theorem delete_exitBranch (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) :
    delete (PruneExit.Bank.directExit g) = none :=
  Proofs.delete_exitBranch g

/-- An exit-only pruning result retains its entire CFG. -/
theorem rewrite_eq_kept_iff :
    rewrite g facts = some (.kept cfg) ↔ PruneExit.Bank.rewrite g facts = some cfg :=
  Proofs.rewrite_eq_kept_iff

/-- Exit deletion consumes the feedback-only pruning result. -/
theorem rewrite_eq_deleted_iff :
    rewrite g facts = some (.deleted clean) ↔
      ∃ cfg, PruneInfeasibleExit.rewrite g facts = some cfg ∧ delete cfg = some clean :=
  Proofs.rewrite_eq_deleted_iff

theorem rewrite_eq_none_iff : rewrite g facts = none ↔ Prune.rewrite g facts = none :=
  Option.map_eq_none_iff

variable {output : Output Γ carried result} {input : Env Γ}

/-- On covered inputs the composed pass preserves actual CFG execution at every budget. -/
theorem rewrite_run_eq (rewritten : rewrite g facts = some output)
    (covered : TupleCovers facts (sourceInputs input)) (fuel : Nat) :
    output.run fuel input = (lower g).run evalOp fuel input :=
  Proofs.rewrite_run_eq rewritten covered fuel

/-- The composed pass preserves the native partial return and its undefinedness. -/
theorem rewrite_denotePart_eq (rewritten : rewrite g facts = some output)
    (covered : TupleCovers facts (sourceInputs input)) :
    output.denotePart input =
      (g.denote model (sourceInputs input)).map (fun value => Outcome.returned (.cons value .nil)) :=
  Proofs.rewrite_denotePart_eq rewritten covered

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit
