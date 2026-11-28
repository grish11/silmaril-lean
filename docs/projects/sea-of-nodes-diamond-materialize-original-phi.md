# Materialize one original Φ before the add peephole

In pinned Simple chapter 8 at `f0a6c6757a795b8e186de0076836a87acef59fa7`,
`ScopeNode.mergeScopes` constructs and peepholes new Φ definitions in
scope-binding index order. A completed Φ computes the meet of its
incoming types, and equal word constants give a constant type.
`Node.peepholeOpt` returns a new constant before running
`PhiNode.idealize`. This happens on the original Φ definition, before
the enclosing add's two-Φ rotation can run. The pinned chapter's
implementation is Java.
[Scope merge order](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/ScopeNode.java#L174-L192) ·
[Φ compute](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/PhiNode.java#L25-L46) ·
[Integer constant meet](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/type/TypeInteger.java#L43-L54) ·
[Constant materialization](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257)

`AddPhi.Rotate.Pair.Dispatch.Materialize.rewrite` takes the same
typed nomination and runtime capture as `Dispatch.rewrite`, plus
the first of the two Φ definitions in source scope order. The join
stores operand positions and has no scope-binding indices. For the
materialization case, the nomination represents separate source Φ
definitions. `.left` identifies the Φ read by the inner add and
`.right` identifies the Φ read by the outer add. The checker
uses actual typed wires and requires two equal explicit word
literals in the selected column. The other column can contain a
runtime operand. When both columns qualify, the supplied first
definition takes priority.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/Defs.lean)

`.materialized` carries one actual typed program. The join exports
the other column at each predecessor and keeps its original producer
table. The suffix contains one literal followed by the two original
add bindings, with the literal wired at the selected operand.
Materializing an original zero emits the literal at this step. The
later add peephole can erase a right-zero addition. The same boundary
leaves the second Φ to its own materialization when both qualify.
Without a checked constant column, the adapter returns the existing
rotated dispatch result or its refusal. The model covers one nominated
definition with uses in this spine, and leaves general discovery,
recursive peepholing and global use cleanup outside scope.
[Later add checks](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L27-L81) ·
[Add construction and peephole](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/Parser.java#L395-L407) ·
[Rotated dispatch](sea-of-nodes-diamond-add-phi-rotate-pair-dispatch.md)

`select_eq_some_iff` fixes exact source-order admission and
`rewrite_eq_ok_iff` fixes the emitted program or delegated result.
`emit_slot_eval_eq` proves agreement at each original predecessor.
`rewrite_returns_iff` covers every typed finite return of both
materialization and delegation.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate.Pair.Dispatch (Refusal)
open AddPhi.Rotate.Pair.Dispatch.Materialize (rewrite)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (word wordPort)

def sample : AddPhi.Pair.Source [.predicate, word] [[wordPort], [wordPort], [wordPort]] where
  shared := .cons (.literal 7) .nil
    (.cons (.literal 7) .nil (.cons (.literal 3) .nil .nil))
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (0 : Fin 3) .head) (.cons (.output (2 : Fin 3) .head) .nil) }
    | .second => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (1 : Fin 3) .head) (.cons (.arg (.tail .head)) .nil) }

def run (guard : Bool) : Except Refusal (BitVec 64) :=
  (rewrite sample (.tail .head) .right).map fun result =>
    result.denote (.cons ⟨guard⟩ (.cons (5 : BitVec 64) .nil))

#eval (run false, run true)

example : (run false, run true) = (.ok 15, .ok 17) := rfl
```

[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Regression
```
