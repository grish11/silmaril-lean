# Dispatch a nominated rotated two-Φ add

`AddPhi.Rotate.Pair.Dispatch.rewrite` is the checked entry point for
`((x + leftΦ) + rightΦ)` on one completed two-predecessor Region.
The typed nomination fixes the two add bindings and the runtime
capture. Each literal row supplies both operands at the same original
predecessor occurrence. Callers pass the diamond and capture port.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Defs.lean)

In Simple chapter 8 at `f0a6c6757a795b8e186de0076836a87acef59fa7`,
an original Φ with equal constant arms materializes before the outer
add is idealized. Dispatch reports `constantColumnPriority` when it
can see that condition, including when the other column has a
nonliteral operand. The resulting source shape can take the
right-zero check, the two-right-constants rule, or the literal-right
rotation, depending on the columns. The straight-line constant-chain
and literal-right APIs have their own typed nominations. This entry
point reports the earlier priority on the two-column input. Other
failed literal lookups report `nonliteralOperand`.
[Original constant materialization](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257) ·
[Add priority](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L27-L90) ·
[Constant chain](sea-of-nodes-pure-add-constant-chain.md) ·
[Literal-right rotation](sea-of-nodes-diamond-add-phi-rotate.md)

When both original columns vary, the two wrapping pair sums determine
the emitted program. Repeated Φ operands are admitted because the
outer identity check compares the inner add with the right Φ.
[Pinned pairing and residual copy](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L96-L131)

| Checked sums | Result and emitted program |
| --- | --- |
| Distinct | `residualPhi` keeps one folded Φ and adds its selected value to the capture. |
| Equal and nonzero | `constantAdd` has an empty join tuple and adds one materialized literal to the capture. |
| Both zero | `captureOnly` has an empty join tuple and returns the capture with no suffix bindings. |

`rewrite_eq_ok_iff` specifies the exact checked rows and emitted
program. `rewrite_returns_iff` gives finite-return equivalence for
every typed input across all three constructors. The native emitters
retain the original Region order and predicate. The scope is one
nominated spine and the immediate right-zero follow-up.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Thms.lean) ·
[Distinct-sum emitter](sea-of-nodes-diamond-add-phi-rotate-pair.md) ·
[Equal-sum emitter](sea-of-nodes-diamond-add-phi-rotate-pair-collapse.md)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate.Pair.Dispatch (Refusal rewrite)
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

def run (a b : BitVec 64) : Except Refusal (BitVec 64) :=
  (rewrite (sample a b) (.tail .head)).map fun result =>
    result.denote (.cons ⟨true⟩ (.cons (5 : BitVec 64) .nil))

#eval (run 3 10, run 3 8, run 1 6)

example : (run 3 10, run 3 8, run 1 6) = (.ok 9, .ok 7, .ok 5) := rfl
```

The regression checks the three emitted constructors, repeated Φs,
reversed occurrence order, wraparound, and the two failure reasons.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Regression
```
