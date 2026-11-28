# Materialize equal sums in the rotated two-Φ add

In Simple chapter 8 at `f0a6c6757a795b8e186de0076836a87acef59fa7`,
`AddNode.phiCon` folds the paired incoming words, constructs a Φ
over those folds, and calls its peephole before copying the residual
add. The Φ computes the meet of its incoming types. When the folded
words agree, that meet is constant, so `Node.peepholeOpt` materializes
one literal before `PhiNode.idealize` can run.
[Pinned rotation](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L96-L131) ·
[Φ type and idealization](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/PhiNode.java#L25-L46) ·
[Integer constant meet](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/type/TypeInteger.java#L43-L54) ·
[Constant materialization priority](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257)

`AddPhi.Rotate.Pair.Collapse.rewrite` uses the same nominated spine,
runtime capture and native two-word join as the distinct-sum rotation.
Its checked literal rows follow the actual predecessor occurrences of
one completed Region. The checker requires both original Φ columns to
vary, then compares their modular pair sums. Varying literal columns
meet to `TypeInteger.BOT` and reach the rotated rule after the original
right-zero and two-right-constants checks. The refusal
`constantOriginalColumn` takes priority over equal sums.
`differentSums` leaves the candidate to the distinct-sum entry point.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Collapse/Defs.lean) ·
[Distinct-sum rotation](sea-of-nodes-diamond-add-phi-rotate-pair.md)

The emitted native program retains the shared table, predicate and
Region order with an empty tuple at the join. For a nonzero sum the
suffix contains one literal and the add of the original captured
argument to that literal. The outer peephole calls `peephole()` on the
replacement add before returning it. If the common sum is zero, that
call takes the initial right-zero branch and returns the original
capture. The zero suffix therefore has no literal or add binding.
This slice models that specific follow-up and keeps the Region
control. General recursion, dead-use cleanup and spine discovery are
outside the proof.
[Residual copy](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L119-L127) ·
[Replacement peephole](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L253-L257) ·
[Right-zero branch](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L27-L43)

`rewrite_eq_ok_iff` specifies exact admission and the emitted program.
`rewrite_slot_eval_eq` proves agreement at each original predecessor,
and `rewrite_returns_iff` proves both directions of finite-return
equivalence for every typed input.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Collapse/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate.Pair.Collapse (Refusal rewrite)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (word wordPort)

def sample (rightFirst rightSecond : BitVec 64) :
    AddPhi.Pair.Source [.predicate, word] [[wordPort], [wordPort], [wordPort], [wordPort]] where
  shared := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 0xfffffffffffffffa) .nil
      (.cons (.literal rightFirst) .nil (.cons (.literal rightSecond) .nil .nil)))
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (0 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil) }
    | .second => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (1 : Fin 4) .head) (.cons (.output (3 : Fin 4) .head) .nil) }

def run (r s : BitVec 64) (guard : Bool) (x : BitVec 64) : Except Refusal (BitVec 64) :=
  (rewrite (sample r s) (.tail .head)).map fun p => p.denote (.cons ⟨guard⟩ (.cons x .nil))

#eval (run 3 8 false 5, run 1 6 true 5)

example : (run 3 8 false 5, run 1 6 true 5) = (.ok 7, .ok 5) := rfl
```

The regression covers both Region orders, equal sums with wraparound,
the zero suffix, and precedence for originally constant columns.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Collapse/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Collapse.Regression
```
