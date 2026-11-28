# Delete the unused zero after the diamond add cleanup

The [inner right-zero cleanup](sea-of-nodes-diamond-cleanup-materialized-phi.md)
leaves two post-join bindings. A zero literal remains, and the surviving add
reads the runtime capture and the selected Φ. This follow-on is an IR cleanup.
It takes the actual program returned by that step and deletes the leading
literal after checking all its potential uses.

`Pure.Deletion.delete?` takes a typed producer nomination and the complete
ordered packet of outgoing wires from that table. It uses the existing
`GVN.Cyclic.Deletion.erase?` on the acyclic dataflow table to validate every
surviving operand. The same partial route must then map every outgoing wire.
A read of the deleted producer causes either check to fail. A client with
several outgoing branches supplies all their packet fields, including the
guard if it reads the table. The checker covers one nominated binding under
the pure, total `Diamond.Model`, with no effects or separate observations
of producer execution. The caller nominates one binding per invocation.
[Packet checker](../../Silmaril/SSA/SeaOfNodes/Pure/Deletion/Defs.lean) ·
[Existing typed erasure](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Deletion/Defs.lean)

`delete?_agrees` preserves each read with a successful map, and
`delete?_outputs_eq` preserves the entire packet. `delete?_opcode_order`
shows that the exact typed opcodes are the original list with the nominated
position erased. The erasure records an exact one-binding decrease.
[Deletion theorems](../../Silmaril/SSA/SeaOfNodes/Pure/Deletion/Thms.lean)

`Cleanup.UnusedZero.rewrite?` nominates a leading zero literal and supplies
the suffix's return wire as the complete outgoing packet. For the suffix from
the inner-add cleanup, `rewrite?_cleaned_shape` gives a single add with the
capture and surviving Φ in that order. `rewrite?_retains_diamond` keeps the
original occurrence-indexed arm wires and their producer scopes.
`rewrite?_returns_iff` and `materialize_then_cleanup_returns_iff` give
finite-return equivalence with the intermediate and original programs for
every typed input. This adapter handles a post-join suffix and leaves other
regions to their own deletion checks.
[Adapter](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/Cleanup/UnusedZero/Defs.lean) ·
[Adapter theorems](../../Silmaril/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/Cleanup/UnusedZero/Thms.lean)

```lean
module

import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Thms
meta import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Materialize.Cleanup.UnusedZero.Defs

open Silmaril.SSA.SeaOfNodes.Diamond
open AddPhi.Rotate.Pair.Dispatch (Refusal)
open AddPhi.Rotate.Pair.Dispatch.Materialize
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
    (Cleanup.rewrite? emitted).bind fun cleaned =>
      (Cleanup.UnusedZero.rewrite? cleaned).map fun target =>
        (target.suffix.sigs.length, target.denote (.cons ⟨guard⟩ (.cons (5 : BitVec 64) .nil)))

#eval (run false, run true)

example : (run false, run true) = (.ok (some (1, 8)), .ok (some (1, 10))) := rfl
```

The regression also checks a reversed Region with an arm-local subtraction,
wrapping addition, and refusal for live uses in a later operand, a return,
and the second field of a multi-field packet.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Diamond/AddPhi/Rotate/Pair/Dispatch/Materialize/Cleanup/UnusedZero/Regression.lean)
