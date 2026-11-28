module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Thms

/-! # Transport checked partial equations through successive entry permutations -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Env Width)
open Silmaril.MLIR.CF.SwitchAssert (Cfg)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

variable {regs mid new : List (ValueSort Width)} {word : Width} {leftSize rightSize : Nat}
variable {leftSource : Source Op regs (.data word) leftSize}
variable {rightSource : Source Op regs (.data word) rightSize}
variable {leftEntry : Fin leftSize} {rightEntry : Fin rightSize}
variable {left : Program leftSource leftEntry} {right : Program rightSource rightEntry}
variable {leftMask rightMask : Mask regs}
variable (first : EntryPermutation regs mid) (second : EntryPermutation mid new)
variable (lhs : Checked left leftMask) (rhs : Checked right rightMask)

/-- Pointwise equation comparison at the valuation of the successively rewired graphs. -/
theorem rvsdg_at_trans_iff (input : Bank (regs := new) model) :
    (graph second (graph first lhs.lower)).denotePart (Join.model model) input =
      (graph second (graph first rhs.lower)).denotePart (Join.model model) input ↔
    left.lower.denotePart (Join.model model) (pull first (pull second input)) =
      right.lower.denotePart (Join.model model) (pull first (pull second input)) := by
  simp only [graph_observe_trans, Equation.rvsdg_observe_eq_native]

/-- Pointwise equation comparison using the actual CFGs compiled with the
successively bound entry names. -/
theorem cf_at_trans_iff (input : Bank (regs := new) model) :
    (Cfg.embed (lowerWith lhs (pull first (cfNames second)))).denotePart evalOp (encodeValues input) =
      (Cfg.embed (lowerWith rhs (pull first (cfNames second)))).denotePart evalOp (encodeValues input) ↔
    left.lower.denotePart (Join.model model) (pull first (pull second input)) =
      right.lower.denotePart (Join.model model) (pull first (pull second input)) := by
  rw [cf_observe_trans, cf_observe_trans]
  exact Equation.cf_at_iff lhs rhs _

/-- Successive rewiring preserves and reflects the native sentence over all valuations. -/
theorem rvsdg_satisfaction_trans :
    (∀ input : Bank (regs := new) model,
      (graph second (graph first lhs.lower)).denotePart (Join.model model) input =
        (graph second (graph first rhs.lower)).denotePart (Join.model model) input) ↔
      (Equation.nativeEquation left right).Holds (Join.model model) := by
  simp only [graph_trans]
  exact rvsdg_satisfaction (first.trans second) lhs rhs

/-- Successive rebinding preserves and reflects the native sentence over
all typed CF environments. -/
theorem cf_satisfaction_trans :
    (∀ input : Env (Widths new),
      (Cfg.embed (lowerWith lhs (pull first (cfNames second)))).denotePart evalOp input =
        (Cfg.embed (lowerWith rhs (pull first (cfNames second)))).denotePart evalOp input) ↔
      (Equation.nativeEquation left right).Holds (Join.model model) := by
  simp only [lowerCF_trans]
  exact cf_satisfaction (first.trans second) lhs rhs

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex
