# Fold a word add of two literal-arm Φs

In Simple chapter 8 at `f0a6c6757a795b8e186de0076836a87acef59fa7`,
the direct two-Φ branch of `AddNode.phiCon` requires both Φs to have
constant operands and the same Region. It keeps that Region, adds
`lphi.in(i)` to `rhs.in(i)` for every incoming occurrence `i`, and
folds the sums using Java `long` arithmetic. `PhiNode.allCons` first
checks that the Region is complete. With two nonconstant Φs of
constants, the right Φ makes `spine_cmp` false and dispatch enters
`phiCon` without a swap. [Pinned add dispatch](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L27-L62) ·
[Two-Φ rule and comparator](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L93-L151) ·
[Completed-Region guard](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/PhiNode.java#L91-L96)

`AddPhi.Pair.rewrite?` uses the native two-word `Diamond.Arms.Graph`
join and one nominated add of its result tuple. Each predecessor slot
supplies one ordered row with the left Φ operand and the right Φ
operand. Both rows belong to the same complete two-predecessor Region
by construction. The interpreter follows the taken projection to its
Region slot before reading that row. The checker scans actual typed
wires in the shared table and each arm's local table for explicit
literals. It rejects either equal-valued column, since that Φ would
materialize a constant earlier. The columns must also differ from
each other in at least one row. This is sufficient to rule out the
earlier same-node doubling branch without Java node identity. Distinct
Java Φ nodes with identical value columns fall outside this admission
check. A zero in just one right occurrence is permitted because the
right Φ is nonconstant.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Pair/Defs.lean) ·
[Constant materialization](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257) ·
[Φ typing](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/PhiNode.java#L25-L35) ·
[Source evaluator's predecessor lookup](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L113-L124)

The result keeps the original shared table, predicate and Region
order. It emits a single folded literal in each arm. The observation
is the fresh Φ's selected value under 64-bit modular addition.
`rewrite?_slot_eval_eq` proves the folded sum at each original slot.
`rewrite?_returns_iff` proves finite-return equivalence for all typed
entries. Equal folded results are supported at this cut, before any
later Φ simplification. Rotation, Java's recursive driver and effects
are outside the scope.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Pair/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model wordPort)

def sample : AddPhi.Pair.Source [.predicate] [[wordPort], [wordPort], [wordPort], [wordPort]] where
  shared := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 0xfffffffffffffffa) .nil
      (.cons (.literal 3) .nil (.cons (.literal 10) .nil .nil)))
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (0 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil) }
    | .second => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (1 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil) }

def result (guard : Bool) : Option (BitVec 64) :=
  (AddPhi.Pair.rewrite? sample).map fun g => (g.denote model (.cons ⟨guard⟩ .nil)).get .head

#eval (result false, result true)

example : (result false, result true) = (some 2, some 4) := rfl
```

The regression also reads an arm-local literal, compares both Region
orders, and rejects a nonliteral operand, a constant Φ column and
identical columns.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Pair/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Regression
```
