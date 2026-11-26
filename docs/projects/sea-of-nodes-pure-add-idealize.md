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
[Pinned comparator](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L134-L151)

| Source case | Checked decision |
| --- | --- |
| Two literal facts | Fold in the original slot using the existing arithmetic rule. |
| Right zero | Erase the add and redirect its reads to the left wire when zero is explicit. A propagated zero without an explicit literal gives a profile refusal. |
| Same source | Check doubling through exact typed wire identity. |
| Non-add on the left and an add on the right | Refuse the source swap. |
| Two add operands | Check the right-spine splice. |
| Two non-add operands | Use the source comparator. A true result selects the unsupported off-spine swap and gives a refusal. |
| Two right constants on a left spine | Check the existing explicit-literal add-chain matcher. If the source branch is selected from propagated facts outside that matcher, report a profile refusal. |
| Later left-spine permutation | Use the source comparator on the actual inner right and outer right wires and check the existing splice. |

A missing ID is an explicit refusal when the applicable comparator
needs both IDs. A failed check at a selected branch produces that
branch's refusal. The prefix has only earlier wires and the opcode
profile has only pure word primitives, so the source's dead self-edge
and Φ cases are outside the input type. This entry point applies one
rewrite at the nomination. The splices emit the fresh intermediate
before the source's recursive peephole.

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
    (.cons .add (.cons (.arg .head) (.cons (.output (0 : Fin 1) .head) .nil)) .nil)
  result := .output (1 : Fin 2) .head

def rewritten := (AddIdealize.step ⟨fun _ => none⟩ sample (.later .here)).map
  (Option.map fun result => AddRewrite.rewrittenProgram sample result.rewrite)

example : rewritten.map (Option.map fun p => p.sigs.length) = .ok (some 1) := rfl
```

The regression covers all six executable branches, literal precedence
over zero and doubling, doubling precedence over rotation, redirected
downstream reads, unsupported swaps, a propagated-zero refusal, and
constant-chain refusal when only the analyzed prefix knows one constant.
The same left spine checks both directions of signed order and missing IDs.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/AddIdealize/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Regression
```
