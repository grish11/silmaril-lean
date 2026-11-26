# Combine constants on a word add spine

Simple chapter 8's `AddNode.idealize` replaces `(x + c₁) + c₂` with
`x + (c₁ + c₂)` and folds the sum of the constants. Its peephole
materializes fully constant results before idealization, and the
addition-by-zero case precedes the spine rule.
[Pinned add-spine rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L66-L74) ·
[Earlier identity and doubling cases](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L33-L43) ·
[Peephole ordering](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L254)

`AddChain.step?` finds one outer addition in the native pure arithmetic
table. Its actual left wire must name an earlier addition whose left wire
has no literal fact. Both right wires must name explicit, nonzero word
literals. The scan keeps literal and addition facts indexed by typed
origins, so a different producer or a reversed operand position cannot
stand in for the inner addition. Two-literal adds and explicit right
zero are left to the existing constant-fold and right-identity rules.

The slot-preserving fold cannot supply an address for a missing
combined literal. This step inserts one `BitVec 64` literal before the
outer add and reuses typed suffix routing. The inner add stays available
to its existing consumers. `step_agrees` proves that every original
producer and argument reads the same value under the returned routing,
and `step_eval_eq` preserves the original return at every typed input.
The original word operations and the combined literal use the same
modular arithmetic.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/AddChain/Defs.lean) ·
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/AddChain/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Thms

open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold.AddChain

def reassociate (p : Program SubZero.Opcode [SubZero.word] SubZero.word) :=
  (step? p).map (rewrittenProgram p)
```

The regression combines `0xffffffffffffffff` and `2` into a newly
bound `1`, then checks the exact rewritten operands of a multiplication
that reads both original additions. It checks a wrapping result, a
different runtime result, and refusal for a subtraction in the left
position, an unknown outer right wire, and a two-literal inner add.
The source slice covers one rewrite on explicit literals. The
[doubling rule](sea-of-nodes-pure-doubling.md) and
[right-spine rotation](sea-of-nodes-pure-right-spine.md) share the same
insertion and routing with the [left-spine step](sea-of-nodes-pure-left-spine.md).
Phi-of-constants push-through remains open.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/AddChain/Regression.lean) ·
[Chapter 8 coverage](sea-of-nodes-pure-sub-self.md#chapter-8-rule-coverage)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Regression
```
