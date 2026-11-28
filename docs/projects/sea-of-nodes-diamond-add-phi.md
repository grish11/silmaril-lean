# Fold a word add through a constant-arm Φ

Simple chapter 8 at `f0a6c6757a795b8e186de0076836a87acef59fa7` handles
the direct case `Φ(a, b) + k` when the left Φ has constant operands and
the right operand is a `ConstantNode`. The non-add-left branch reaches
`phiCon` because a constant on the right makes `spine_cmp` false.
`phiCon` keeps the left Φ's Region and folds one add per predecessor
position. Java `long` addition corresponds to the native 64-bit modular
word add. [Pinned dispatch and comparison](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L27-L62) ·
[Pinned `phiCon`](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L93-L151) ·
[Word addition](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L15-L24)

`AddPhi.rewrite?` takes a native `Diamond.Graph` and the typed shared
wire for the right operand of one enclosing return add. The native
graph returns the selected Φ value. `SourceReturns` composes that finite
return with the additional add use. The checker looks up both actual
Φ wires and the right wire in the typed producer table and requires
explicit word literals. It rejects equal arm values and a zero right
literal, which have earlier constant-materialization and right-zero
cases. The native control type supplies a complete Region with two
predecessors and one matching operand per slot. A constant RHS makes
the source's two-Φ same-Region check inapplicable.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Defs.lean) ·
[Constant materialization](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257) ·
[Φ typing and all-constant guard](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/PhiNode.java#L25-L35) ·
[`PhiNode.allCons`](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/PhiNode.java#L91-L96) ·
[Unequal integer constants meet to a nonconstant](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/type/TypeInteger.java#L43-L54)

The result is an existing `Diamond.Arms.Graph` with one folded literal
in each arm. The shared prefix, predicate and Region order are retained.
The native interpreter follows the If projection to its actual Region
slot and evaluates just that arm. `rewrite?_slot_eval_eq` proves
agreement at each predecessor, and `rewrite?_returns_iff` preserves and
reflects the finite return for every typed entry. The checked view
covers a single return use. It specializes completed active diamonds
with explicit literals. Rotated spines, a second Φ, dead or unfinished
Regions, and Java graph mutation and recursive cleanup are outside
this slice.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Thms.lean) ·
[Source evaluator's predecessor lookup](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/GraphEvaluator.java#L113-L124)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (model wordPort)

def sample : AddPhi.WordGraph [.predicate] [[wordPort], [wordPort], [wordPort]] where
  dataflow := .cons (.literal 0xffffffffffffffff) .nil
    (.cons (.literal 7) .nil (.cons (.literal 1) .nil .nil))
  predicate := .arg .head
  phi := ⟨⟨.onFalse⟩, fun
    | .first => .output (0 : Fin 3) .head
    | .second => .output (1 : Fin 3) .head⟩

def folded := AddPhi.rewrite? sample (.output (2 : Fin 3) .head)

def result (guard : Bool) : Option (BitVec 64) :=
  folded.map fun g => (g.denote model (.cons ⟨guard⟩ .nil)).get .head

#eval (result false, result true)

example : (result false, result true) = (some 0, some 8) := rfl
```

The regressions compare both predecessor orders, exercise modular
wraparound, and reject right zero, an equal-arm Φ and a nonliteral arm.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Regression
```
