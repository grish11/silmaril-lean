# Rewrite same-source word addition as multiplication by two

Simple chapter 8's `AddNode.idealize` tests `lhs == rhs` and builds
`MulNode(lhs, ConstantNode(2))`. Its peephole materializes constant
results before idealization. The addition-by-zero case also precedes
the doubling check.
[Pinned AddNode.idealize](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L33-L43) ·
[Pinned Node.peepholeOpt](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L254)

`Doubling.step?` finds the first eligible addition in the native
pure word table. It checks the actual typed operand origins and inserts
a fresh word literal two through the same insertion and routing used
by the [add-chain rewrite](sea-of-nodes-pure-add-constant-chain.md).
`match_exact` proves acceptance requires identical typed wires.
`match_refuses_literal` gives the existing forward literal fold priority,
including facts propagated from earlier bindings. An addition of a
runtime wire and a distinct zero literal is left to the existing
right-identity pass.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Doubling/Defs.lean) ·
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Doubling/Thms.lean)

`step_agrees` preserves the value of every original producer and
argument under the returned typed routing. `step_eval_eq` preserves
the result at every input in the native `BitVec 64` model.

```lean
module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Thms

open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold

def double? (p : Program SubZero.Opcode [SubZero.word] SubZero.word) :=
  (Doubling.step? p).map (AddRewrite.rewrittenProgram p)

def sample : Program SubZero.Opcode [SubZero.word] SubZero.word where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg .head) .nil)) .nil
  result := .output (0 : Fin 1) .head

example : (double? sample).map (fun p => p.sigs.length) = some 2 := rfl
```

The regression checks exact rewiring through a downstream use. Doubling
the signed minimum wraps to zero. Distinct typed wires with equal fixture
inputs are refused, explicit and propagated literals still fold, and
the existing right-identity pass can erase the addition feeding the
new multiplication. This is one local rewrite in the word profile.
General spine rotation, ordering by node ID, and Phi push-through remain
open in the source checklist.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/Doubling/Regression.lean) ·
[Chapter 8 coverage](sea-of-nodes-pure-sub-self.md#chapter-8-rule-coverage)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddChain.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.Doubling.Regression
```
