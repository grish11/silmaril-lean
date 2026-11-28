# Discover carried word classes on two native feedback occurrences

`Discovery.discover` enumerates every typed word slot of the existing
`Quads.Loop.Tail.TwoBackedges.Program`. The initial classes group
equal structural keys at the end of the ordered preheader. Each round
seeds the header with the current classes and computes the true and
false feedback keys independently from that completed header. The
next class key consists of the old class and the ordered pair of
feedback keys. Operand order inside each structural key is retained.
The pass materializes each round's labels and feedback keys in finite
tables before it compares or refines them.
[Discovery definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Discovery/Defs.lean) ·
[Native two-feedback checker](sea-of-nodes-gvn-cyclic-feedback-families.md)

The old class in the key prevents merges. Every unstable round splits
at least one class, and the number of classes is bounded by the number
of word slots. The default budget is that slot count. More precisely,
`run_stable_of_fuel` suffices with the slot count minus the starting
class count. The final partition is stable under the same feedback
key computation and refines the initial entry classes.
`normalize_fixed` states stability as equality of the same-class
relation after another round.
[Refinement theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Discovery/Thms.lean)

For a finer partition and any coarsening, `feedbackKeys_coarsen`
replaces each typed argument leaf of the finer key with the key at
that slot in the actual coarse family seed. The result is exactly
the pair of keys computed under the coarse partition. The substitution
preserves literals, opcodes, and operand order. It commutes with
numbering the header and each feedback block independently.
`refine_monotone` then preserves the refinement order.
`stable_refines_run` relates any stable candidate to every finite
run prefix that starts with a coarser partition. Since
`initial_eq_iff` characterizes the entry classes by their structural
keys, `normalize_coarsest` proves that the discovered partition is the
coarsest stable structural refinement of those entry classes, up to
the same-class relation.

Discovery emits one equation for each nonrepresentative slot, using
the first member of its class in register order. The existing
`Family.certify?` checks these equations. The proof shows that entry
and both feedback checks succeed for the discovered family. Passing
the original result slot to `Discovery.certify?` always produces a
native invariant certificate. When proposing another return slot,
admission additionally requires matching post-header keys.
`same_class_at_arrival` proves word equality at any native header
arrival. A checked redirect preserves the actual occurrence and
complete packet and every common-budget result from the original
input bank.
[Family certificate](sea-of-nodes-gvn-cyclic-feedback-families.md)

```lean
module
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Thms

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort)
open GVN.Cyclic.FixedPoint (Refines)
open GVN.Cyclic.TwoBackedges (WordSlot)
open GVN.Cyclic.TwoBackedges.Family.Discovery
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Program)

example {regs : List (ValueSort Unit)} (p : Program Opcode regs word) :
    (certify? p p.result).isSome = true :=
  certify?_original_isSome p

example {regs : List (ValueSort Unit)} (p : Program Opcode regs word)
    (candidate : Classes regs) (stable : Stable p candidate) (entry : Refines candidate (initial p)) :
    Refines candidate (normalize p) :=
  normalize_coarsest p stable entry

example {regs : List (ValueSort Unit)} (p target : Program Opcode regs word)
    (replacement : WordSlot regs) (input : Bank (regs := regs) model)
    (accepted : rewrite? p replacement = some target) (fuel : Nat) :
    target.source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input :=
  rewrite_run_eq p accepted fuel input
```

The existing mutually inductive fixture discovers both equations
without nominations and admits the existing return redirect. Reversing
one subtraction on the false feedback edge splits the first pair in
round one. Its dependent pair stays together in that round, then
splits in round two because the header now reads different classes.
The resulting stable partition admits the invariant certificate and
refuses the proposed replacement return. On the unchanged fixture,
a separately supplied discrete partition assigns labels in reverse
slot order. It passes the stability check and refines every executable
round, while the discovered partition keeps the two mutually inductive
pairs together. The finer keys of the first pair differ, and substitution
into the discovered seed recovers both ordered coarse feedback keys.
[Executable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Regression.lean)

```sh
topic=SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family
make check CHECK_TARGETS="+Silmaril.$topic.Discovery.Thms +Silmaril.Proofs.$topic.Regression"
lake env leanchecker "Silmaril.$topic.Discovery.Thms"
lake env leanchecker "Silmaril.Proofs.$topic.Regression"
```

Click's dissertation §§4.1–4.2 motivates splitting cyclic classes by
the class of each ordered input. This implementation recomputes keys
synchronously on the two actual ordered blocks. It proves stability
from the structural entry seed, structural coarseness, and soundness
through the native family certificate. Completeness for semantic equality, general CFG worklists,
automatic return-slot selection, and producer deletion remain outside
this slice. Click PLDI ’95 §3.1 step 3 motivates the optional checked
return replacement.
[Pinned dissertation](sea-of-nodes-gvn-cyclic.md#sources) ·
[Pinned PLDI paper](sea-of-nodes-gvn-cyclic-pass.md#sources)
