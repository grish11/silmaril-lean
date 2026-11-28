# Discover checked edits on a materialized diamond suffix

In Simple chapter 8 at `f0a6c6757a795b8e186de0076836a87acef59fa7`,
`Node.peepholeOpt` handles constant results before `AddNode.idealize`.
Right-zero returns the left operand before doubling or the add-spine
rules. Discovery asks the existing `AddIdealize.step` to choose the
rule. It admits literal folding, right-zero and the off-spine
literal-right swap. For the swap, the dispatcher reaches
`spine_cmp` with two non-add operands. The comparator rejects a known
literal on the right and moves a known literal from the left to the
right. With no signed source IDs, a pair of ordinary runtime operands
cannot take that comparison. The earlier literal and right-zero
decisions keep their priority. Unused-producer erasure is a separate
checked IR operation. Simple's recursive Java peepholing and global
worklist are outside this profile.
[Constant priority](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257)
· [AddNode order](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L15-L63)
· [Literal comparison](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L134-L151)

`Pure.SuffixReplay.Discovery.normalize` works on the existing replay
block, whose outgoing packet starts with the word return and includes
all additional uses. It scans the current typed producer table in
dependency order for the first eligible add decision, preserving
the checker's priority at each producer. If that scan fails it
scans for exact add reuse, then for the first producer admitted by
`Pure.Deletion.delete?` with the complete packet. It re-enumerates
after each edit, so a candidate always belongs to the current table.
Signed source IDs are unnecessary for this subset. The executed rule
list and composed partial route are available in the result.
[Discovery definitions](../../Silmaril/SSA/SeaOfNodes/Pure/SuffixReplay/Discovery/Defs.lean) ·
[Typed replay and packet semantics](sea-of-nodes-diamond-suffix-replay.md)

Exact add reuse calls `GVN.Pass.eliminateCandidate?` on an add
candidate. The existing key checks the opcode and ordered typed
operand wires. Its earlier representative is available at the
candidate's prefix in this straight-line table. Elimination routes
both the surviving uses and the complete outgoing packet, then
removes the redundant add. Equal computed results and reversed
operand pairs alone give no exact match. The rule is local to the
post-join suffix, with no cross-block placement or cyclic refinement.
[Acyclic GVN proof and paper pin](sea-of-nodes/optimization/sea-of-nodes-gvn-pass.md)

Cliff Click's *Global Code Motion/Global Value Numbering*, PLDI ’95,
§3.1 step 3, gives the replacement-and-removal correspondence.
Simple chapter 8 leaves GVN to a later chapter. At the same pinned
revision, chapter 9 compares the node class and ordered input
identities, and reuses a previously interned node. This pass retains
its own table-order scheduling and uses the checked earlier-wire
witness in place of Java hash-table interning.
[PLDI ’95](https://doi.org/10.1145/207110.207154)
· [Chapter 8 GVN placeholder](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257)
· [Chapter 9 reuse](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter09/src/main/java/com/seaofnodes/simple/node/Node.java#L267-L295)
· [Chapter 9 ordered equality](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter09/src/main/java/com/seaofnodes/simple/node/Node.java#L433-L450)

The primary measure is the binding count plus the number of add
operators. Literal folding keeps the binding count and decreases the
add count. Right-zero and unused deletion each remove one binding and
decrease the primary measure. An admitted swap keeps both counts and
strictly decreases the number of adds with a known literal only on the
left, using the same typed prefix facts as the dispatcher. Adding up
these occurrences includes ones an earlier branch may preempt.

The fuel measure is the square of the primary measure plus the
literal-left count. The latter is bounded by the number of bindings,
so every strict primary decrease lowers the fuel measure even if it
exposes new literal-left operands. With the primary measure fixed, a
swap lowers the fuel measure directly. `normalize_count` counts
erasures separately and bounds all edits by the initial measure. One
extra unit of fuel lets the driver perform the last scan.

`reuseAdd?_eq_none_iff` characterizes the exact-key check on adds.
`normalize_noEligible` covers the three admitted add idealizations,
exact add reuse and unused deletion with the complete packet. `normalize_stable` certifies that a
second run makes no further edits. `normalize_agrees` preserves mapped
reads through the replay route, and `normalize_packet_eq` preserves
all packet values.
[Discovery theorems](../../Silmaril/SSA/SeaOfNodes/Pure/SuffixReplay/Discovery/Thms.lean)

`Materialize.SuffixReplay.Discovery.normalize` uses the actual emitted
program and the word return as its packet. It preserves the capture
and the entire occurrence-indexed diamond. The two
`materialize_then_normalize_*` theorems preserve and reflect finite
returns and their absence for every typed input of the original
two-Φ graph.
[Diamond theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/SuffixReplay/Discovery/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.SuffixReplay.Discovery.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate.Pair.Dispatch (Refusal)
open AddPhi.Rotate.Pair.Dispatch.Materialize
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model word wordPort)
open Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay (Block)
open Silmaril.SSA.RVSDG (Tuple)

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

def run (guard : Bool) : Except Refusal (Option (Nat × BitVec 64)) :=
  (rewrite sample (.tail .head) .left).map fun result => do
    let .materialized .right _ emitted := result | none
    let target := SuffixReplay.Discovery.normalize emitted
    pure (target.suffix.sigs.length, target.denote (.cons ⟨guard⟩ (.cons (5 : BitVec 64) .nil)))

#eval (run false, run true)

example : (run false, run true) = (.ok (some (1, 8)), .ok (some (1, 10))) := rfl

def wrappingTail : Block [word] [wordPort] where
  sigs := [[wordPort], [wordPort], [wordPort], [wordPort]]
  flow := .cons (.literal 0xffffffffffffffff) .nil (.cons (.literal 1) .nil
    (.cons .add (.cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil))
      (.cons .add (.cons (.arg .head) (.cons (.output (2 : Fin 3) .head) .nil)) .nil)))
  packet := .cons (.output (3 : Fin 4) .head) (.cons (.output (2 : Fin 4) .head) .nil)

def folded := Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize wrappingTail

def summary : List Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.Rule × Nat × BitVec 64 × BitVec 64 :=
  let block := folded.state.block
  let entry : Tuple (Val model.value) (dataPorts [word]) := .cons (5 : BitVec 64) .nil
  let values := block.packet.read entry (block.flow.eval model entry PUnit.unit)
  (folded.rules, block.sigs.length, values.get .head, values.get (.tail .head))

#eval summary

example : summary = ([.literal, .rightZero, .deleteUnused, .deleteUnused], 1, 5, 0) := rfl

def literalLeftZero : Block [word] [] where
  sigs := [[wordPort], [wordPort]]
  flow := .cons (.literal 0) .nil
    (.cons .add (.cons (.output (0 : Fin 1) .head) (.cons (.arg .head) .nil)) .nil)
  packet := .cons (.output (1 : Fin 2) .head) .nil

def ordered := Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize literalLeftZero

#eval (ordered.rules, ordered.state.block.packet.addresses)

example : ordered.rules = [.literalRight, .rightZero, .deleteUnused] ∧
    ordered.state.block.packet.addresses = [.arg 0] := ⟨rfl, rfl⟩

def repeated : Block [word, word] [wordPort] where
  sigs := [[wordPort], [wordPort]]
  flow := .cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil))
    (.cons .add (.cons (.arg .head) (.cons (.arg (.tail .head)) .nil)) .nil)
  packet := .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil)

def sharedAdd := Silmaril.SSA.SeaOfNodes.Pure.SuffixReplay.Discovery.normalize repeated

#eval (sharedAdd.rules, sharedAdd.state.block.packet.addresses)

example : sharedAdd.rules = [.reuseAdd] ∧
    sharedAdd.state.block.packet.addresses = [.output 0 0, .output 0 0] := ⟨rfl, rfl⟩
```

The regression checks that the emitted right-column zero is live
before the redirect and is then discovered for deletion. It verifies
the remaining wrapping add and its original Φ wires in a reversed
Region. The stock materialization suffix has a literal and runtime
arguments for the capture and Φ, so the literal-fold fixture appends
a typed tail to the actual emitted table. It folds
`0xffffffffffffffff + 1` to zero, exposes a right-zero erasure and
keeps the folded zero live through the second packet field. The two
input literals become unused. Another typed tail exposes an off-spine
swap on the emitted return through a non-add relay. Left zero enables
erasure, and a nonzero literal moves right once. Both cases check the
ordered surviving operands and the full packet on both predecessors.
A pair of runtime inputs stays in its original order. For exact reuse,
the fixture appends a second copy of the actual materialized inner add
and observes its downstream subtraction and outgoing packet use.
The surviving add feeds both the original outer add and the new
subtraction. With reversed operands, both producers stay live and
the packet reads keep distinct addresses.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/SuffixReplay/Discovery/Regression.lean)
