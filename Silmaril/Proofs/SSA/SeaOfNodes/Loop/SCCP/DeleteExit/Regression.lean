module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit

open Diamond.SCCP (TupleCovers)
open PruneExit.Example.Bank (i8 i16)
open PruneInfeasibleExit.Example (Carried facts graph input)
open SeaOfNodes.MLIR (Word sourceInputs)
open Loop.MLIR.CF (evalOp)
open Loop.MLIR.CF.Bank (lower)
open Silmaril.MLIR.CF (Terminator)

private def cleaned : HeaderCfg [i8] Carried i16 :=
  (delete (PruneInfeasibleExit.directFeedback graph)).get (by decide)

private theorem deleted : delete (PruneInfeasibleExit.directFeedback graph) = some cleaned := rfl
private theorem rewritten : rewrite graph (facts (.constant 0)) = some (.deleted cleaned) := rfl

example : cleaned.entry.eval evalOp (fun term env => Terminator.eval env term) (input 0) =
    .inl ⟨.header, .cons 1 (.cons 300 (.cons 4 .nil))⟩ := rfl

-- The third element reads the old first element, before the first is replaced.
example :
    (cleaned.block .header).eval evalOp (fun term env => Terminator.eval env term)
      (.cons 1 (.cons 300 (.cons 4 (input 0)))) = .inl ⟨.header, .cons 4 (.cons 302 (.cons 2 .nil))⟩ :=
  rfl

example : rewrite graph (facts (.constant 1)) = some (.kept (PruneExit.Bank.directExit graph)) := rfl
example : delete (lower graph) = none := rfl

example : Example.run (.constant 0) 8 0 = some (true, none) := rfl
example : Example.run (.constant 1) 3 1 = some (false, some 300) := rfl
example : rewrite graph (facts .overdefined) = none := rfl
example : rewrite graph (facts .bottom) = none := rfl
example : Example.refusesVarying = true := rfl

private theorem covered (flag : Word i8) : TupleCovers (facts (.constant flag)) (sourceInputs (input flag)) := by
  intro sort port
  cases port with
  | head => rfl
  | tail p => cases p

example (fuel : Nat) : cleaned.run evalOp fuel (input 0) = (lower graph).run evalOp fuel (input 0) :=
  rewrite_run_eq rewritten (covered 0) fuel

example (fuel : Nat) : cleaned.run evalOp fuel (input 0) = none := by
  rw [run_eq deleted]
  exact (PruneInfeasibleExit.runs_none (g := graph) (facts := facts (.constant 0)) rfl (covered 0) fuel).1

example : (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed cleaned).denotePart evalOp (input 0) = Part.none :=
  (denotePart_eq deleted (input 0)).trans
    (PruneInfeasibleExit.denotePart_eq_none (g := graph) (facts := facts (.constant 0)) rfl (covered 0))

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.DeleteExit
