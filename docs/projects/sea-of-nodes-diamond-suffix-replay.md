# Replay checked edits on a materialized diamond suffix

In Simple chapter 8 at `f0a6c6757a795b8e186de0076836a87acef59fa7`,
`Node.peepholeOpt` handles constant results before `AddNode.idealize`.
The add checks right-zero before doubling, swapping and spine
rewrites. Those are the per-add priorities already modeled by
`AddIdealize.step`. The driver uses that checker on native word
operators in a straight-line suffix. It supplies no signed source IDs,
so requests that require one can refuse. Unused-producer deletion is
a separate IR check. The caller's finite request list sets the order
and bound for replay. Java's recursive optimization, use-driven
scheduling, and fixed points are outside the scope.
[Constant results and recursion](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257)
· [Add rule order](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L15-L88)

`Pure.SuffixReplay.run` takes a pure producer table and a complete
ordered outgoing packet. Its first field is the word return, followed
by any additional outgoing use. Each request names a typed wire of
the initial table. Replay routes it to its current value source and
uses the existing typed lookup in the actual current table. An
idealization may redirect that value to another producer or to an
argument. A request for an argument reports that it has no producer.
An erasure by `Pure.Deletion.delete?` removes the candidate's route,
so any following request for it reports `.stale`. Shifted addresses
cannot silently retarget an erased nomination. A failure reports the
first request index and reason and carries no graph.
[Driver](../../Silmaril/SSA/SeaOfNodes/Pure/SuffixReplay/Defs.lean)

`compose_agrees` and `run_agrees` preserve values on the composed
partial map and route the complete packet. `run_packet_eq` states
equality of all its values for every typed input. `runFrom_append`
relates replay of a concatenated request list to the checked prefix
and the continuation on its current table. `runFrom_refuses_at`
specifies the result of a failing request after an accepted prefix.
[Driver theorems](../../Silmaril/SSA/SeaOfNodes/Pure/SuffixReplay/Thms.lean)

`Materialize.SuffixReplay.rewrite` runs that driver on the emitted
post-join suffix, where the return wire is the complete packet.
`rewrite_preserves` retains the entire diamond, including the
predecessor order and Φ operand wires, as well as the original
runtime capture. `materialize_then_rewrite_returns_iff` and
`materialize_then_rewrite_no_return_iff` cover every typed input of
the original two-Φ graph after successful materialization and replay.
[Diamond theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/SuffixReplay/Thms.lean)

The example uses a zero in the **right** column of a reversed Region.
Materialization puts the zero on the outer add's right. Replay applies
right-zero at that add, then checks and drops the unused literal.
Repeating the deletion request fails at index 2. The regression also
checks a repeated idealization request that follows an actual
redirection to a different producer, and a refusal when a second
packet field still reads the zero.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/SuffixReplay/Regression.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Defs
import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Defs
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate.Pair.Dispatch (Refusal)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay (Failure)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (word wordPort)

def sample : AddPhi.Pair.Source [.predicate, word] [[wordPort], [wordPort]] where
  shared := .cons (.literal 3) .nil (.cons (.literal 0) .nil .nil)
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil) }
    | .second => {
        sigs := [], dataflow := .nil
        outputs := .cons (.arg (.tail .head)) (.cons (.output (1 : Fin 2) .head) .nil) }

def run (guard repeatZero : Bool) : Except Refusal (Option (Except Failure (Nat × BitVec 64))) :=
  (rewrite sample (.tail .head) .left).map fun result => do
    let .materialized .right _ emitted := result | none
    let zero ← Cleanup.UnusedZero.leadingZero? emitted.suffix
    let cut : SuffixReplay.Request emitted := ⟨.deleteUnused, zero.origin⟩
    let requests := [⟨.idealize, emitted.suffix.result⟩, cut] ++ if repeatZero then [cut] else []
    pure ((SuffixReplay.rewrite emitted requests).map fun target =>
      (target.suffix.sigs.length, target.denote (.cons ⟨guard⟩ (.cons (5 : BitVec 64) .nil))))

#eval (run false false, run true false, run false true)

example : (run false false, run true false, run false true) =
    (.ok (some (.ok (1, 8))), .ok (some (.ok (1, 10))), .ok (some (.error ⟨2, .stale⟩))) := rfl
```
