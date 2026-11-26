module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Thms
import Silmaril.Proofs.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Correctness
import Silmaril.SSA.SeaOfNodes.Quads.Thms

/-! # Identity and composition of typed entry reindexing -/

public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex

open SeaOfNodes.Diamond (ValueSort dataPorts)
open SeaOfNodes.Loop.MLIR.CF (Op model evalOp)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open RVSDG (Dialect PortType Tuple Wires)
open RVSDG.NestedTheta (Graph)
open Blocks (Bank)
open Blocks.Prune (Mask)
open Diamond.Prune (Checked)

universe u v w

theorem pull_refl {T : Type u} {F : T → Type w} {ports : List T} (input : Tuple F ports) :
    pull (Permutation.refl ports) input = input :=
  Quads.tabulate_get_eq input

/-- Pulling back a valuation reads the second interface before the first. -/
theorem pull_trans {T : Type u} {F : T → Type w} {old mid new : List T}
    (first : Permutation old mid) (second : Permutation mid new) (input : Tuple F new) :
    pull first (pull second input) = pull (first.trans second) input :=
  Proofs.pull_trans first second input

section Graph

variable {V S : Type u} {Φ : Dialect.{u, v} V S}
variable {old mid new outs : List (PortType V S)} {past sigs : List (List (PortType V S))}

theorem wires_refl (bundle : Wires old past outs) :
    wires (Permutation.refl old) bundle = bundle :=
  Proofs.wires_refl bundle

theorem wires_trans (first : Permutation old mid) (second : Permutation mid new)
    (bundle : Wires old past outs) :
    wires second (wires first bundle) = wires (first.trans second) bundle :=
  Proofs.wires_trans first second bundle

theorem graph_refl (g : Graph Φ old past sigs outs) :
    graph (Permutation.refl old) g = g :=
  Proofs.graph_refl g

/-- Two successive outer rewirings equal one first-to-second composition. -/
theorem graph_trans (first : Permutation old mid) (second : Permutation mid new)
    (g : Graph Φ old past sigs outs) :
    graph second (graph first g) = graph (first.trans second) g :=
  Proofs.graph_trans first second g

theorem graph_run_trans (first : Permutation old mid) (second : Permutation mid new)
    (g : Graph Φ old [] sigs outs) (m : RVSDG.Model.{u, v, w} Φ)
    (fuel : Nat) (input : Tuple m.Val new) :
    (graph second (graph first g)).run m fuel input = (graph (first.trans second) g).run m fuel input := by
  rw [graph_trans]

end Graph

variable {regs mid new : List (ValueSort Width)} {out : ValueSort Width} {size : Nat}
variable {src : Source Op regs out size} {entry : Fin size}
variable {p : Program src entry} {mask : Mask regs}

theorem cfNames_refl : cfNames (Permutation.refl (dataPorts regs)) = entryNames regs :=
  pull_refl _

/-- Sequential rebinding and composed rebinding name the exact same
external CF variables in original register order. -/
theorem cfNames_trans (first : EntryPermutation regs mid) (second : EntryPermutation mid new) :
    pull first (cfNames second) = cfNames (first.trans second) :=
  pull_trans first second _

theorem lowerCF_refl (checked : Checked p mask) :
    lowerCF (Permutation.refl (dataPorts regs)) checked = Pruned.lower checked :=
  congrArg (lowerWith checked) cfNames_refl

/-- Both name tables feed the same checked emitter. Its fixed label
family includes the original projected header bank. -/
theorem lowerCF_trans (first : EntryPermutation regs mid) (second : EntryPermutation mid new)
    (checked : Checked p mask) :
    lowerWith checked (pull first (cfNames second)) = lowerCF (first.trans second) checked :=
  congrArg (lowerWith checked) (cfNames_trans first second)

theorem cf_run_trans (first : EntryPermutation regs mid) (second : EntryPermutation mid new)
    (checked : Checked p mask) (fuel : Nat) (input : Bank (regs := new) model) :
    (lowerWith checked (pull first (cfNames second))).run evalOp fuel (encodeValues input) =
      (lowerCF (first.trans second) checked).run evalOp fuel (encodeValues input) := by
  rw [lowerCF_trans]

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex
