module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Institution.RuntimeObservation.Defs
public import Silmaril.SSA.MLIR.CF.SwitchAssert.Denotation.Defs

/-! # Native and projected equations at a common quad diamond boundary -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Equation

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op evalOp)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.SwitchAssert (Cfg Outcome)
open RVSDG.NestedTheta.Institution.RuntimeObservation (Sentence)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

abbrev signature : RVSDG.Institution.Signature (ValueSort Width) PEmpty :=
  ⟨Join.Opcode Op⟩

variable {regs : List (ValueSort Width)} {w : Width} {leftSize rightSize : Nat}
variable {leftSource : Source Op regs (.data w) leftSize}
variable {rightSource : Source Op regs (.data w) rightSize}
variable {leftEntry : Fin leftSize} {rightEntry : Fin rightSize}
variable {left : Program leftSource leftEntry} {right : Program rightSource rightEntry}
variable {leftMask rightMask : Mask regs}

/-- Use the existing nested runtime sentence on the native γ/θ graphs. -/
def nativeEquation (left : Program leftSource leftEntry) (right : Program rightSource rightEntry) :
    Sentence signature :=
  .equation ⟨_, left.lower⟩ ⟨_, right.lower⟩

/-- The two projected graphs retain the typed entry and word result interfaces. -/
def prunedEquation (lhs : Checked left leftMask) (rhs : Checked right rightMask) :
    Sentence signature :=
  .equation ⟨_, lhs.lower⟩ ⟨_, rhs.lower⟩

/-- Observe the actual emitted CFG through the existing Basic CF embedding. -/
noncomputable def observeCF (checked : Checked left leftMask) (input : Env (Widths regs)) :
    Part (Outcome [w]) :=
  (Cfg.embed (lower checked)).denotePart evalOp input

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Equation
