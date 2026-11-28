# Replay checked Simple word-add replacements

In Simple chapter 8 at revision `f0a6c6757a795b8e186de0076836a87acef59fa7`,
`Node.peepholeOpt` computes a type and handles constant materialization
before calling `idealize`. On a replacement it calls `n.peephole()` and
then runs cleanup based on the old node's uses. The literal-left swap
returns the same add node. Its next call can take the right-zero rule.
[Pinned continuation](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L276) ·
[Right-zero rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L36-L39) ·
[Off-spine swap](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L59-L63)

`AddIdealize.Replay.run` starts at a single typed word producer in the
native acyclic non-Φ profile. It invokes `AddIdealize.step` and follows the
original nomination through each accepted edit's typed routing. A routed
output is looked up by exact typed address in the rewritten table. All
edits committed so far are included in the returned rewrite, even if a
later step refuses. The rule trace lists the accepted edits in order.
[Definition](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/AddIdealize/Replay/Defs.lean) ·
[Single-step precedence](sea-of-nodes-pure-add-idealize.md)

| Stop | Meaning |
| --- | --- |
| `noEdit` | The single-step checker returned successfully without an edit. |
| `argument` | The accepted rewrite routed the nomination to an input argument. |
| `refused reason` | The checker declined the nomination, for example because an ID is missing or the routed producer is outside the add rules. |
| `unresolvedProducer` | The routed output did not resolve in the typed word-producer enumeration. |
| `fuelExhausted` | No budget remains to run the checker at the next producer. |

Each accepted edit spends one unit of fuel. A route to an argument
terminates immediately and costs no extra fuel. The supplied signed
source IDs stay valid across in-place swaps. After any other accepted
edit, replay retains argument IDs and discards output IDs, including
evidence it could potentially recover from surviving producers. This
keeps fresh outputs without invented IDs.
[Java node-ID allocation](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L55-L69)

`run_agrees` proves equality along the composed map for every original
typed read and input valuation. `run_eval_eq` preserves the return under
the same modular word model, and `run_rules_le` bounds the trace length
by the supplied fuel. This is bounded single-nomination replay. Java's
recursive treatment of fresh intermediate nodes, allocation order,
use-driven cleanup and Φ behavior are outside the theorem.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/AddIdealize/Replay/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.Thms
meta import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Defs
meta import Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.Defs

open Silmaril.SSA.SeaOfNodes.Pure
open ConstantFold
open SubZero (word)

def sample : Program SubZero.Opcode [word] word where
  dataflow := .cons (.literal 0) .nil
    (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil)) .nil)
  result := .output (1 : Fin 2) .head

def replayed := AddIdealize.Replay.run 2 ⟨fun _ => none⟩ sample (.later .here)

#eval (replayed.rules, replayed.stop)

example : replayed.rules = [.offSpineSwap, .rightZero] ∧
    (replayed.rewrite.route sample.result).address = .arg 0 := ⟨rfl, rfl⟩
```

The regression checks the exact rewritten multiplication operands and
shifted return address, the wrapping result, the fuel stop after one
swap, and the distinction between missing signed IDs and a false
comparison.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Pure/ConstantFold/AddIdealize/Replay/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Pure.ConstantFold.AddIdealize.Replay.Regression
```
