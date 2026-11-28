# Apply one source-ordered Simple word-add rewrite

`AddIdealize.step` takes a native word program, a typed
`GVN.Producer` nomination and the optional signed source IDs used by
`LeftSpine`. It analyzes the original prefix, then decides which branch
applies at that producer. A successful edit returns its rule and typed
routing. `.ok none` represents a comparator result with no edit.
`.error` gives the reason a nominated rewrite was refused.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/AddIdealize/Defs.lean) ·
[Source ID contract](sea-of-nodes-pure-left-spine.md)

The pinned Simple revision is `f0a6c6757a795b8e186de0076836a87acef59fa7`.
`Node.peepholeOpt` materializes constants before calling
`AddNode.idealize`. The dispatcher uses this order in the acyclic,
non-Φ word profile.
[Word constant evaluation](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L15-L24) ·
[Literal precedence](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257) ·
[Pinned AddNode.idealize](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L27-L90) ·
[Pinned comparator](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L134-L151) ·
[In-place swap](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L347-L353)

| Source case | Checked decision |
| --- | --- |
| Two literal facts | Fold in the original slot using the existing arithmetic rule. |
| Right zero | Erase the add and redirect its reads to the left wire when zero is explicit. A propagated zero without an explicit literal gives a profile refusal. |
| Same source | Check doubling through exact typed wire identity. |
| Non-add on the left and an add on the right | Swap the actual wires at the original add slot before considering right-spine rotation. This guard uses producer shape. |
| Two add operands | Check the right-spine splice. |
| Two non-add operands | Swap at the original slot if the source comparator returns true. A left literal can win without IDs. For two nonliterals the comparator uses the supplied signed source IDs. |
| Two right constants on a left spine | Check the existing explicit-literal add-chain matcher. If the source branch is selected from propagated facts outside that matcher, report a profile refusal. |
| Later left-spine permutation | Use the source comparator on the actual inner right and outer right wires and check the existing splice. |

A missing ID is an explicit refusal when the applicable comparator
needs both IDs. A false comparison gives `.ok none`. Both swaps use
one typed binding replacement with identity routing, so the input
source-ID map still applies. A failed check at a selected branch
produces that branch's refusal. The prefix has only earlier wires and the opcode
profile has only pure word primitives, so the source's dead self-edge
and Φ cases are outside the input type. This entry point applies one
rewrite at the nomination. The splices emit the fresh intermediate
before the source's recursive peephole.
[Follow a replacement with bounded replay](sea-of-nodes-pure-add-replay.md)

`step_agrees` proves that every original read agrees along the
returned routing. `step_eval_eq` preserves the return for all inputs
under native 64-bit modular semantics.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/AddIdealize/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Thms

open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold
open SubZero (word)

def sample : Program SubZero.Opcode [word] word where
  dataflow := .cons (.literal 0) .nil
    (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil)) .nil)
  result := .output (1 : Fin 2) .head

def rewritten := (AddIdealize.step ⟨fun _ => none⟩ sample (.later .here)).map
  (Option.map fun result => (result.rule, AddRewrite.rewrittenProgram sample result.rewrite))

example : rewritten.map (Option.map fun (rule, p) => (rule, p.sigs.length)) =
    .ok (some (.offSpineSwap, 2)) := rfl
```

The regression covers all eight executable branches, literal precedence
over zero and doubling, doubling precedence over rotation, redirected
downstream reads, the non-add-left swap before rotation, a propagated-zero
refusal, and constant-chain refusal when only the analyzed prefix knows
one constant.
The off-spine fixture distinguishes true, false, and missing signed
evidence. Swapping `0 + x` yields `x + 0` for a subsequent idealization step.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/AddIdealize/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Regression
```
