# Erase the inner right-zero add after Φ materialization

Simple chapter 8 at `f0a6c6757a795b8e186de0076836a87acef59fa7` folds
constant results before calling `AddNode.idealize`. The captured
runtime input has no compile-time literal in this profile. When the
materialized left Φ supplies zero, the inner add already has zero on
the right. The source returns its left operand before doubling,
swapping or comparing the add spine. The comparator can move a
left-hand literal to the right in a different nomination. Materializing
the right Φ in this spine places the literal on the **outer** add's
right. A zero there is outside this inner-add cleanup.
[Node constant fold](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/Node.java#L243-L257)
· [Add order](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L15-L62)
· [Spine comparator](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter08/src/main/java/com/seaofnodes/simple/node/AddNode.java#L134-L151)

`Materialize.Cleanup.rewrite?` consumes the actual result of the
[original-column materialization](sea-of-nodes-diamond-materialize-original-phi.md).
The matcher inspects the typed suffix, including the capture, the
producer of the inner RHS, the outer add's two ordered operands and
the returned wire. It nominates the matched inner producer to
`AddIdealize.step` and accepts only `.rightZero`. That branch needs no
signed node IDs.

The returned program keeps the capture and the entire diamond,
including the Region order and the surviving Φ wire at each
predecessor. Its suffix keeps the literal and has one add
`capture + survivingPhi`. The old inner result redirects to the
capture and the old outer result moves from producer 2 to producer 1.
The adapter leaves rotated results, nonzero cases and other suffix
shapes to the caller. This step leaves dead-literal removal, outer-add
cleanup and recursive Java peepholing outside its scope.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/Cleanup/Defs.lean)

`suffixEdit?_redirects` gives the exact wiring and
`suffixEdit?_agrees` preserves every original suffix read through the
typed map. `rewrite?_atSlot_eq` preserves the result at each predecessor
occurrence. `rewrite?_returns_iff` and
`materialize_then_rewrite?_returns_iff` preserve and reflect finite
returns against the intermediate and original programs, respectively,
for all typed inputs.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/Cleanup/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate.Pair.Dispatch (Refusal)
open AddPhi.Rotate.Pair.Dispatch.Materialize (rewrite)
open AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup (rewrite?)
open Silmaril.SSA.SeaOfNodes.Pure.SubZero (word wordPort)

def sample : AddPhi.Pair.Source [.predicate, word] [[wordPort], [wordPort]] where
  shared := .cons (.literal 0) .nil (.cons (.literal 3) .nil .nil)
  predicate := .arg .head
  merge := ⟨.onFalse⟩
  arms
    | .first => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (0 : Fin 2) .head) (.cons (.output (1 : Fin 2) .head) .nil) }
    | .second => {
        sigs := [], dataflow := .nil
        outputs := .cons (.output (0 : Fin 2) .head) (.cons (.arg (.tail .head)) .nil) }

def run (guard : Bool) : Except Refusal (Option (Nat × BitVec 64)) :=
  (rewrite sample (.tail .head) .right).map fun emitted =>
    (rewrite? emitted).map fun cleaned =>
      (cleaned.suffix.sigs.length,
        cleaned.denote (.cons ⟨guard⟩ (.cons (5 : BitVec 64) .nil)))

#eval (run false, run true)

example : (run false, run true) = (.ok (some (2, 8)), .ok (some (2, 10))) := rfl
```

The regression also uses an arm-local subtraction as the live Φ
operand. It covers reversed Region order, a wrapping return, refusal
of nonzero and outer-zero cases, and a left tag paired with the wrong
actual suffix.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/Cleanup/Regression.lean)
