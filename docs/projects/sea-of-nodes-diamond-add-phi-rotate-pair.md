# Rotate a word-add spine through two literal-arm Φs

In Simple chapter 8 at `f0a6c6757a795b8e186de0076836a87acef59fa7`,
`AddNode.idealize` calls `phiCon(this, true)` after the earlier
two-right-constants rule and before the final spine comparison.
The rotated case checks that the inner producer has the same class
as the outer add. It takes the first Φ from `lhs.in(2)`, requires the
right Φ to belong to the same Region, and folds the two operands at
each predecessor index. The remaining add copies `lhs.in(1)` as its
left operand.
[Pinned dispatch](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L27-L90) ·
[Pinned rotation, Region check and operand order](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L93-L131)

`AddPhi.Rotate.Pair.rewrite?` takes one native two-word
`Diamond.Arms.Graph` join and a typed runtime input port for `x`.
The fixed source suffix is `((x + leftΦ) + rightΦ)`. Each predecessor
row supplies both Φ operands in the same completed two-slot Region.
The shared literal checker resolves the actual typed operand wires
in each row. Both columns must vary across the two occurrences, so
neither Φ would already materialize a constant. This also excludes
the earlier right-zero and constant-chain cases. The input capture
cannot be a self-edge of the inner add. For the inner `x + leftΦ`,
the comparator leaves the Φ on the right, and the runtime argument
offers no left Φ to push through.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Defs.lean) ·
[Shared literal pairing](sea-of-nodes-diamond-add-phi-pair.md) ·
[Residual capture and suffix](sea-of-nodes-diamond-add-phi-rotate.md) ·
[Completed-Region and Φ typing guards](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/PhiNode.java#L25-L35) ·
[`PhiNode.allCons`](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/PhiNode.java#L91-L96) ·
[Inner comparison](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L134-L151)

The outer doubling test compares the inner `AddNode` with the right
`PhiNode`. The two Φ operands may therefore refer to the same node.
The rotated guard admits repeated columns when their folded sums
differ. Equal sums take the source's constant materialization on
the newly constructed Φ, so this checker declines that output shape.
[Equal-sum materialization checker](sea-of-nodes-diamond-add-phi-rotate-pair-collapse.md) ·
[Outer identity test](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L36-L43) ·
[Constant materialization](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257)

The emitted program keeps the shared table, predicate and Region.
It links the single folded Φ to one actual post-join add that reads
the original runtime capture. `rewrite?_slot_eval_eq` proves agreement
at each original predecessor and `rewrite?_returns_iff` proves finite
return equivalence for all typed inputs under 64-bit modular
arithmetic. The checker covers one nominated spine with a runtime
input and two literal-arm Φs. Arbitrary spine discovery, recursive
Java peepholing, and use-driven cleanup are outside this proof.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Thms.lean) ·
[Source evaluator's predecessor lookup](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L113-L124)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (word wordPort)

def sample : AddPhi.Pair.Source [.predicate, word] [[wordPort], [wordPort], [wordPort], [wordPort]] where
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

def result (guard : Bool) (x : BitVec 64) : Option (BitVec 64) :=
  (AddPhi.Rotate.Pair.rewrite? sample (.tail .head)).map
    fun p => p.denote (.cons ⟨guard⟩ (.cons x .nil))

#eval (result false 5, result true 5)

example : (result false 0xffffffffffffffff, result true 0xffffffffffffffff) =
    (some 1, some 3) := rfl
```

The regression checks both Region orders, exact emitted literals and
suffix, wrapping sums, repeated Φ operands, and refusal of a
nonliteral operand, a constant original column, and equal folded sums.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Pair.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Regression
```
