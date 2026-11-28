module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Correctness

/-! # Observation and equation satisfaction under typed entry permutations -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex

open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Env Width)
open RVSDG (Dialect PortType Port Tuple)
open RVSDG.NestedTheta (Graph)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

universe u v w

theorem pull_get {T : Type u} {F : T → Type w} {old new : List T}
    (order : Permutation old new) (input : Tuple F new) {t : T} (port : Port old t) :
    (pull order input).get port = input.get (order t port) :=
  Proofs.pull_get order input port

theorem pull_surjective {T : Type u} {F : T → Type w} {old new : List T}
    (order : Permutation old new) : Function.Surjective (pull order : Tuple F new → Tuple F old) :=
  Proofs.pull_surjective order

section Graph

variable {V S : Type u} {Φ : Dialect.{u, v} V S}
variable {old new outs : List (PortType V S)} {sigs : List (List (PortType V S))}
variable (order : Permutation old new) (m : RVSDG.Model.{u, v, w} Φ)
variable (g : Graph Φ old [] sigs outs) (input : Tuple m.Val new)

/-- Reindexing the outer graph wires keeps each loop activation budget and
uses the corresponding original valuation. -/
theorem graph_run (fuel : Nat) :
    (graph order g).run m fuel input = g.run m fuel (pull order input) :=
  Proofs.graph_run order m fuel g input

theorem graph_observe :
    (graph order g).denotePart m input = g.denotePart m (pull order input) :=
  Proofs.graph_observe order m g input

end Graph

variable {regs external : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {p : Program src entry} {mask : Mask regs}
variable (order : EntryPermutation regs external)

/-- The re-emitted CFG uses the original fuel and returns at the encoded
valuation selected by the same typed entry permutation. -/
theorem cf_run (checked : Checked p mask) (fuel : Nat) (input : Bank (regs := external) model) :
    (lowerCF order checked).run evalOp fuel (encodeValues input) =
      (Pruned.lower checked).run evalOp fuel (encodeValues (pull order input)) :=
  Proofs.cf_run order checked fuel input

theorem cf_observe {w : Width} {src : Source Op regs (.data w) size} {entry : Fin size}
    {p : Program src entry} (checked : Checked p mask) (input : Bank (regs := external) model) :
    observeCF order checked (encodeValues input) =
      Equation.observeCF checked (encodeValues (pull order input)) :=
  Proofs.cf_observe order checked input

variable {word : Width} {leftSize rightSize : Nat}
variable {leftSource : Source Op regs (.data word) leftSize}
variable {rightSource : Source Op regs (.data word) rightSize}
variable {leftEntry : Fin leftSize} {rightEntry : Fin rightSize}
variable {left : Program leftSource leftEntry} {right : Program rightSource rightEntry}
variable {leftMask rightMask : Mask regs}

theorem native_satisfaction (left : Program leftSource leftEntry) (right : Program rightSource rightEntry) :
    (nativeEquation order left right).Holds (Join.model model) ↔
      (Equation.nativeEquation left right).Holds (Join.model model) :=
  Proofs.native_satisfaction order left right

theorem rvsdg_satisfaction (lhs : Checked left leftMask) (rhs : Checked right rightMask) :
    (prunedEquation order lhs rhs).Holds (Join.model model) ↔
      (Equation.nativeEquation left right).Holds (Join.model model) :=
  Proofs.rvsdg_satisfaction order lhs rhs

theorem cf_satisfaction (lhs : Checked left leftMask) (rhs : Checked right rightMask) :
    (∀ input : Env (Widths external), observeCF order lhs input = observeCF order rhs input) ↔
      (Equation.nativeEquation left right).Holds (Join.model model) :=
  Proofs.cf_satisfaction order lhs rhs

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex
