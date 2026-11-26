module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Example.Defs

/-! # Two noncommuting word swaps in a mixed entry layout -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Example

open CF.Example (checked regs source)
open Pruned.Example (accepted)
open Reindex.Example (external word bit movePredicate original)
open SeaOfNodes.Loop.MLIR.CF (evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Blocks (Bank)

def swapResultStride : EntryPermutation external external :=
  (Permutation.swap word word [bit, word, word]).under [word, word]

def swapSelectorResult : EntryPermutation external external :=
  (Permutation.swap word word [word, bit, word, word]).under [word]

def first : EntryPermutation regs external := movePredicate.trans swapResultStride
def second : EntryPermutation external external := swapSelectorResult
def reversed : EntryPermutation regs external := (movePredicate.trans swapSelectorResult).trans swapResultStride

def paired : Bank (regs := external) model := pull (first.trans second).symm original

def predicateBit : Nat :=
  ((encodeValues paired).get (.there (.there (.there (.there .here))))).toNat

def predecessors : List Nat :=
  (checked.trace model 3 ((source 4).body.eval model (pull (first.trans second) paired))).map
    (fun occurrence => (checked.predecessor occurrence).val)

/-- Execute the successive rewiring and the successive CF name selections. -/
def sequentialResults : Option Nat × Option Nat :=
  (((graph second (graph first accepted.lower)).run (Join.model model) 3 paired).map
      (fun values => (values.get .head).toNat),
    ((lowerWith accepted (pull first (cfNames second))).run evalOp 16 (encodeValues paired)).map
      (fun env => (env.get .here).toNat))

def results (order : EntryPermutation regs external) : Option Nat × Option Nat :=
  (((graph order accepted.lower).run (Join.model model) 3 paired).map (fun values => (values.get .head).toNat),
    ((lowerCF order accepted).run evalOp 16 (encodeValues paired)).map (fun env => (env.get .here).toNat))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Composition.Example
