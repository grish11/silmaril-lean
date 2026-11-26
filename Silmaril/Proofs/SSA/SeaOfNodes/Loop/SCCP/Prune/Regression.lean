module

import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Example.Defs
import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune.Thms

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune

open Diamond.SCCP (TupleCovers)
open PruneInfeasibleExit.Example (Carried facts graph input)
open PruneExit.Example.Bank (i8 i16)
open SeaOfNodes.MLIR (Word sourceInputs)
open Loop.MLIR.CF (TargetOp evalOp model)
open Loop.MLIR.CF.Bank (Label lower)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Terminator)
open Silmaril.MLIR.Pure (Code)

private def directSuccessor {Δ : List Width} : Code TargetOp (Terminator (Label Carried i16) [i16]) Δ → Option Bool
  | .terminator (.br edge) => some (PruneExit.Bank.isHeader edge.label)
  | .terminator _ => none
  | .letOp _ _ rest => directSuccessor rest

private theorem exitRewrite :
    rewrite graph (facts (.constant 1)) = some (PruneExit.Bank.directExit graph) := rfl

private theorem feedbackRewrite :
    rewrite graph (facts (.constant 0)) = some (PruneInfeasibleExit.directFeedback graph) := rfl

example : (rewrite graph (facts (.constant 1))).bind (fun cfg => directSuccessor (cfg.block .header)) =
    some false := rfl
example : (rewrite graph (facts (.constant 0))).bind (fun cfg => directSuccessor (cfg.block .header)) =
    some true := rfl

example : Example.run (.constant 1) 3 1 = some (some 300) := rfl
example : Example.run (.constant 1) 2 1 = some none := rfl
example : Example.run (.constant 0) 8 0 = some none := rfl

example : (solve model graph (facts .overdefined)).1 =
    {incomingIndex .entry, incomingIndex .backedge, exitIndex} := rfl
example : (solve model graph (facts .bottom)).1 = {incomingIndex .entry} := rfl
example : rewrite graph (facts .overdefined) = none := rfl
example : rewrite graph (facts .bottom) = none := rfl
example : Example.refusesVarying = true := rfl

private theorem covered (flag : Word i8) : TupleCovers (facts (.constant flag)) (sourceInputs (input flag)) := by
  intro sort port
  cases port with
  | head => rfl
  | tail p => cases p

example (budget : Nat) : (PruneExit.Bank.directExit graph).run evalOp budget (input 1) =
    (lower graph).run evalOp budget (input 1) :=
  run_eq exitRewrite (covered 1) budget

example :
    (Silmaril.MLIR.CF.SwitchAssert.Cfg.embed (PruneInfeasibleExit.directFeedback graph)).denotePart evalOp
      (input 0) = Part.none :=
  PruneInfeasibleExit.denotePart_eq_none (g := graph) (facts := facts (.constant 0)) rfl (covered 0)

example (budget : Nat) : (PruneInfeasibleExit.directFeedback graph).run evalOp budget (input 0) =
    (lower graph).run evalOp budget (input 0) :=
  run_eq feedbackRewrite (covered 0) budget

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune
