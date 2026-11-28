module

public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Defs
public import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Example.Defs

/-! # Permute a mixed typed entry before two feedback edges -/

@[expose] public section

namespace Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Example

open CF.Example (checked input num regs source test)
open Pruned.Example (accepted)
open SeaOfNodes.Diamond (ValueSort)
open SeaOfNodes.Loop.MLIR.CF (evalOp model)
open SeaOfNodes.MLIR.Lowering (encodeValues)
open Silmaril.MLIR.Arith (Width)
open Blocks (Bank)

abbrev external : List (ValueSort Width) := [num, num, num, num, .predicate, num, num]
abbrev word : SeaOfNodes.Diamond.Ty Width := .value num
abbrev bit : SeaOfNodes.Diamond.Ty Width := .value .predicate

/-- Move the last predicate before the two final word positions. -/
def movePredicate : EntryPermutation regs external := fun t =>
  (((Permutation.swap word bit []).under [word, word, word, word, word]) t).trans
    (((Permutation.swap word bit [word]).under [word, word, word, word]) t)

/-- The result and stride also exchange their external positions. -/
def order : EntryPermutation regs external := fun t =>
  (((Permutation.swap word word [word, word, bit]).under [word, word]) t).trans (movePredicate t)

def original : Bank (regs := regs) model := Quads.write test ⟨true⟩ input
def paired : Bank (regs := external) model := pull order.symm original

/-- This still has the new typed interface, but omits the word exchange. -/
def wrongPairing : Bank (regs := external) model := pull movePredicate.symm original

def predicateBit : Nat :=
  ((encodeValues paired).get (.there (.there (.there (.there .here))))).toNat

def predecessors : List Nat :=
  (checked.trace model 3 ((source 4).body.eval model (pull order paired))).map
    (fun occurrence => (checked.predecessor occurrence).val)

def results (input : Bank (regs := external) model) (activations fuel : Nat) : Option Nat × Option Nat :=
  (((graph order accepted.lower).run (Join.model model) activations input).map
      (fun values => (values.get .head).toNat),
    ((lowerCF order accepted).run evalOp fuel (encodeValues input)).map (fun env => (env.get .here).toNat))

end Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Pruned.Reindex.Example
