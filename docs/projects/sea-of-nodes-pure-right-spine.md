# Rotate a right-hand word add spine

Simple chapter 8 handles two-constant evaluation, right zero, and
same-source doubling before reaching the add-spine rules. If only the
right operand is an add, Java takes the earlier swap. The next return
rotates `x + (y + z)` into `(x + y) + z`, with `x` itself an add at
that point. The later `spine_cmp` and its node-ID tie break apply to a
different branch.
[Pinned AddNode.idealize](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L33-L74) ·
[Pinned spine_cmp](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L134-L150)

`RightSpine.step?` implements that rotation in the native acyclic word
table. Its forward scan checks two distinct add producers with no
literal facts in the existing arithmetic fact domain. It records each
addition's actual typed operands in order. `match_exact` identifies the
ordered right-hand pair used in the edit. The earlier non-add-left swap
and same-source doubling stay outside this matcher. The existing
[add-chain step](sea-of-nodes-pure-add-constant-chain.md) covers two
right literals on a left spine.

The edit keeps the old right add and inserts a private `x + y` before
the replacement. The replacement reads that fresh sum and then `z`.
This is the source rotation before Java recursively peepholes the fresh
inner add. The shared `AddRewrite` splice accepts the fresh word binding
and routes the original result and suffix. `step_agrees` proves that
every original typed read is preserved under that routing.
`step_eval_eq` preserves the return at every input using wrapping
`BitVec 64` arithmetic.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/RightSpine/Defs.lean) ·
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/RightSpine/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Thms

open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold
open SubZero (word)

def rotateOnce (p : Program SubZero.Opcode [word, word, word] word) :=
  (RightSpine.step? p).map (AddRewrite.rewrittenProgram p)

def sample : Program SubZero.Opcode [word, word, word] word where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons .add (.cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil))
      (.cons .add (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)) .nil))
  result := .output (2 : Fin 3) .head

example : (rotateOnce sample).map (fun p => p.sigs.length) = some 4 := rfl
```

The regression checks the exact wiring for `(a + b) + (c + d)`, a
wraparound in the private sum, and a downstream multiplication that
still reads the original right add. It also checks refusal for the
earlier swap, a non-add right operand, same-source doubling, and an
add that the literal scan predicts to be zero. This step performs at
most one rotation. Non-add-left swaps, ordered left-spine rotations,
and Phi push-through remain separate.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/RightSpine/Regression.lean) ·
[Chapter 8 coverage](sea-of-nodes-pure-sub-self.md#chapter-8-rule-coverage)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Regression
```
