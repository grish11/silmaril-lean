module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Comparison.Equation.Correctness

/-! # Independent satisfaction bridges for the two projected targets -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Equation

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Env Width)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

variable {regs : List (ValueSort Width)} {w : Width} {leftSize rightSize : Nat}
variable {leftSource : Source Op regs (.data w) leftSize}
variable {rightSource : Source Op regs (.data w) rightSize}
variable {leftEntry : Fin leftSize} {rightEntry : Fin rightSize}
variable {left : Program leftSource leftEntry} {right : Program rightSource rightEntry}
variable {leftMask rightMask : Mask regs}

/-- Every typed CF environment encodes a native valuation, including
the one-bit encodings of predicate slots. -/
theorem encodeValues_surjective (regs : List (ValueSort Width)) :
    Function.Surjective (encodeValues (ins := regs)) :=
  Proofs.encodeValues_surjective regs

/-- Projection preserves the native numbered graph's partial observation. -/
theorem rvsdg_observe_eq_native (checked : Checked left leftMask) (input : Bank (regs := regs) model) :
    checked.lower.denotePart (Join.model model) input = left.lower.denotePart (Join.model model) input :=
  Proofs.rvsdg_observe_eq_native checked input

/-- At each typed native valuation CF equality reflects the native equation. -/
theorem cf_at_iff (lhs : Checked left leftMask) (rhs : Checked right rightMask)
    (input : Bank (regs := regs) model) :
    observeCF lhs (encodeValues input) = observeCF rhs (encodeValues input) ↔
      left.lower.denotePart (Join.model model) input = right.lower.denotePart (Join.model model) input :=
  Proofs.cf_at_iff lhs rhs input

/-- The existing runtime-observation sentences agree before and after projection. -/
theorem rvsdg_satisfaction (lhs : Checked left leftMask) (rhs : Checked right rightMask) :
    (prunedEquation lhs rhs).Holds (Join.model model) ↔ (nativeEquation left right).Holds (Join.model model) :=
  Proofs.rvsdg_satisfaction lhs rhs

/-- CF satisfies the equation over every typed CF valuation exactly when the
native nested graphs agree over every native valuation. -/
theorem cf_satisfaction (lhs : Checked left leftMask) (rhs : Checked right rightMask) :
    (∀ input : Env (Widths regs), observeCF lhs input = observeCF rhs input) ↔
      (nativeEquation left right).Holds (Join.model model) :=
  Proofs.cf_satisfaction lhs rhs

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Equation
