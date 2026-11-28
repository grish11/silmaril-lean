# Permute a word add spine using the source comparator

Simple chapter 8's later add-spine branch builds `(x + z) + y` from
`(x + y) + z` when `spine_cmp(y, z)` is true. In the non-Φ profile the
executable comparator first rejects a literal `z`, then prefers moving
a literal `y` to the right. For two nonliterals it tests
`z._nid > y._nid`. Java allocates these signed `int` IDs at node
construction.
[Pinned idealization](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L83-L88) ·
[Pinned comparator](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L134-L151) ·
[Source ID allocation](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L55-L64)

`SourceIds` supplies optional `Int32` values keyed by the input
table's typed wire addresses. Source correspondence assumes the
supplied values are the corresponding Java nodes' IDs. For two
nonliteral wires an absent ID makes `compare?` return `none`.
`SourceIds.atWire_weaken` proves that extending a prefix keeps the
ID lookup for a previous wire. `compare_of_ids` states the comparison
on supplied values, and `compare_nonliteral_iff` gives the exact
success condition for two nonliteral wires. Each call uses an ID map
for its own input table.

`LeftSpine.step?` requires a left add result, a distinct non-add
right wire, and no literal facts for the two outer operands in the
existing prefix fact domain. This leaves literal folds, right zero,
doubling, right-spine rotation, and the two-right-constant add-chain
case to their earlier branches. The acyclic table gives each
producer only arguments and earlier wires. `match_exact` identifies
the admitted wiring. The shared splice inserts the private `x + z`
and uses it with the original `y` in the replacement.
`step_agrees` and `step_eval_eq` preserve every original read and
the return for every input under modular `BitVec 64` addition.
[Earlier source branches](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L33-L82) ·
[Definitions](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/LeftSpine/Defs.lean) ·
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/LeftSpine/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.Thms

open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold
open SubZero (word)

def ids : LeftSpine.SourceIds where
  lookup
    | .arg 2 => some 25
    | .arg 1 => some 31
    | _ => none

def sample : Program SubZero.Opcode [word, word, word] word where
  dataflow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail (.tail .head))) .nil))
    (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg (.tail .head)) .nil)) .nil)
  result := .output (1 : Fin 2) .head

example : ((LeftSpine.step? ids sample).map (AddRewrite.rewrittenProgram sample)).map
    (fun p => p.sigs.length) = some 3 := rfl
```

The regression uses a greater source ID for an earlier native
producer, reverses the supplied IDs on the same graph, and checks
refusal for equal or missing IDs. It also checks the literal case
without IDs, earlier-rule refusals, exact routing, and wraparound
in the private sum. The emitted fragment corresponds to one source
permutation before recursive peepholing of the fresh inner sum.
The ordered dispatcher also handles the earlier non-Φ swaps. The
checklist tracks the remaining Φ and recursive cases.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/LeftSpine/Regression.lean) ·
[Ordered dispatcher](sea-of-nodes-pure-add-idealize.md) ·
[Chapter 8 coverage](sea-of-nodes-pure-sub-self.md#chapter-8-rule-coverage)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.RightSpine.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.LeftSpine.Regression
```
