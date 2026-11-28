# Rotate a word-add spine through a literal-arm Φ

In Simple chapter 8 at `f0a6c6757a795b8e186de0076836a87acef59fa7`,
the rotated literal-right case starts at `((x + Φ(a, b)) + k)`.
`phiCon` checks that the inner producer has the same class as the
outer add, then looks for the Φ at `lhs.in(2)`. It folds `a + k` and
`b + k` at their original incoming positions. The replacement
`op.copy(lhs.in(1), phi)` keeps `x` as the left operand of the
remaining add.
[Pinned `phiCon`](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L93-L131)

`AddPhi.Rotate.rewrite?` takes the original Diamond, a typed runtime
argument port for `x`, and the actual shared wire for `k`. The
nomination fixes a word add in each binding and the precise order of
their operands. The original suffix reads `x` and the selected Φ at its
first add, then adds `k` to that result. The checker reuses
`AddPhi.rewrite?` to check that the Φ operands are explicit literals
with different values and that `k` is a nonzero explicit literal. The
native profile has one complete two-predecessor Region.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Defs.lean) ·
[Direct literal checker](sea-of-nodes-diamond-add-phi.md)

The runtime input plays the role of Simple's nonconstant argument
projection. For the inner `x + Φ`, a right Φ of constants prevents the
off-spine swap, and the direct `phiCon` call has no Φ on the left
to push through. At the outer add, the nonzero literal excludes
right-zero, the literal and inner add are different node kinds, and the
typed acyclic spine excludes the dead self-edge. Distinct Φ arm values
keep the Φ's type nonconstant, so the earlier two-right-constants rule
cannot take the candidate. The rotated Φ branch comes before the final
spine comparison. An equal-arm Φ belongs to earlier constant
materialization.
[Runtime projection](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/Parser.java#L105-L109) ·
[Outer priority](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L27-L90) ·
[Inner comparison](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L134-L151) ·
[Φ typing](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/PhiNode.java#L25-L35)

The emitted program links the native folded diamond to an actual
straight-line suffix with one typed add. Its continuation takes the
original captured argument and the selected folded word, in that
order. `rewrite?_slot_eval_eq` checks the composition at each original
predecessor using modular associativity, and `rewrite?_returns_iff`
preserves and reflects finite returns at all typed entries. The
checker covers the nominated orientation with one literal RHS and one
runtime argument capture. Extracting arbitrary post-join spines,
rotating with a second Φ, and recursive Java peepholing and cleanup
are outside this slice.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (word wordPort)

def sample : AddPhi.WordGraph [.predicate, word] [[wordPort], [wordPort], [wordPort]] where
  dataflow := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 7) .nil (.cons (.literal 2) .nil .nil))
  predicate := .arg .head
  phi := ⟨⟨.onFalse⟩, fun
    | .first => .output (0 : Fin 3) .head
    | .second => .output (1 : Fin 3) .head⟩

def result (guard : Bool) (x : BitVec 64) : Option (BitVec 64) :=
  (AddPhi.Rotate.rewrite? sample (.tail .head) (.output (2 : Fin 3) .head)).map
    fun p => p.denote (.cons ⟨guard⟩ (.cons x .nil))

#eval (result false 5, result true 5)

example : (result false 0xffffffffffffffff, result true 0xffffffffffffffff) =
    (some 0, some 8) := rfl
```

The regression checks exact emitted operands and the residual suffix,
wraparound, a reversed Region, changing runtime inputs, and the
right-zero, equal-arm and nonliteral-right refusals.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Regression
```
