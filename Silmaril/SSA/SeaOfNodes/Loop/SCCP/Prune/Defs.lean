module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.PruneExit.Defs

/-! Analyze once and keep the unique feasible successor of the emitted MLIR loop. -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune

open PruneExit (InputFacts)
open Loop.MLIR.CF (TargetOp model)
open Loop.MLIR.CF.Bank (Label)
open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Cfg)

/-- Follow the tail-test polarity: true retains feedback, false retains exit.
Equal marks mean there is no unique choice. -/
def uniqueSuccessor (edges : Executable) : Option Bool :=
  match decide (incomingIndex .backedge ∈ edges), decide (exitIndex ∈ edges) with
  | true, false => some true
  | false, true => some false
  | _, _ => none

variable {Γ carried : List Width} {result : Width} {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- Compute the simultaneous solution once and reuse the existing branch
selector. Return `none` when both tail successors or neither are marked. -/
def rewrite (g : Loop.MLIR.CF.Bank.Program Γ carried result entrySigs headerSigs) (facts : InputFacts Γ) :
    Option (Cfg TargetOp (Label carried result) Γ [result]) :=
  let edges := (solve model g facts).1
  (uniqueSuccessor edges).map (fun feedback => PruneExit.Bank.selectHeader feedback g)

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Prune
