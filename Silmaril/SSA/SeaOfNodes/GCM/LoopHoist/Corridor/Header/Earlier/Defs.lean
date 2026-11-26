module

public import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Defs

/-! # Move one nominated header binding earlier to the selected cut -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier

open Silmaril.MLIR.Arith (Width)
open Silmaril.MLIR.CF (Block Cfg)
open Loop.MLIR.CF (Program TargetOp lower)

variable {Input Γ : List Width} {carried result : Width}
variable {entrySigs headerSigs : List (List (Diamond.Ty Width))}

/-- The exact operation symbol with its operand signature and result width. -/
abbrev Operation := (args : List Width) × (width : Width) × TargetOp args width

/-- Project the binding order, ignoring the de Bruijn names of operands. -/
def operations : {Γ : List Width} →
    Block TargetOp (SourceLabel carried result) Γ [result] → List Operation
  | _, .terminator _ => []
  | _, .letOp op _ rest => ⟨_, _, op⟩ :: operations rest

/-- From position `target + extraSteps + 1`, move the binding left one
position at a time. Each next swap checks the newly typed block. -/
def moveEarlier? (target : Nat) : Nat →
    Block TargetOp (SourceLabel carried result) Γ [result] →
      Option (Block TargetOp (SourceLabel carried result) Γ [result])
  | 0, block => swapAt? target block
  | extraSteps + 1, block => do
    let block ← swapAt? (target + extraSteps + 1) block
    moveEarlier? target extraSteps block

/-- The destination is a cut in the original CFG. A successful result
installs a header only after every intervening check has passed. -/
def moveAt? (cfg : Cfg TargetOp (SourceLabel carried result) Input [result])
    (index : Nat) (cut : Point (SourceLabel carried result)) :
    Option (Cfg TargetOp (SourceLabel carried result) Input [result]) :=
  let _ := sourceTargetDecEq carried result
  let insertion := afterRemoval index cut.cut
  if cut.block = headerId ∧ insertion < index then
    (moveEarlier? insertion (index - insertion - 1) (cfg.block .header)).map (withHeader cfg)
  else none

/-- Rank the exact def/use sites once on the input CFG. Return that original
cut alongside the emitted CFG. Intermediate swap indices are local to the
successive typed headers. -/
def pickAndMove? (g : Program Input carried result entrySigs headerSigs) (index : Nat) :
    Option (Point (SourceLabel carried result) × Cfg TargetOp (SourceLabel carried result) Input [result]) :=
  pickAndEmit? g index moveAt?

end Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Earlier
