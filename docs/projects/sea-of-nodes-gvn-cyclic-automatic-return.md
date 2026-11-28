# Automatic return representative for native two-feedback GVN

`Return.returnOrigin` reads the returned register's reaching version from
the existing typed quad transfer for the actual header. The policy
applies when that origin is precisely the original carried argument.
A header assignment can leave a new producer in the returned register,
in which case the policy leaves the program unchanged.
[Return selection](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Discovery/Return/Defs.lean) ·
[Native header transfer](../../Silmaril/SSA/SeaOfNodes/Quads/CFG/Defs.lean)

Among the slots in the normalized structural class of the carried
return, `best` chooses the least original register index whose
completed-header key matches the return key. The exit check uses the
actual header definitions, so an earlier member overwritten with a
different key is ineligible. The original carried slot is always
eligible. A singleton or an already canonical return stays unchanged.
`optimize` submits any selected change to the existing family checker
and rewrites only the return operand.
[Selection and preservation laws](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Discovery/Return/Thms.lean) ·
[Family certificate](sea-of-nodes-gvn-cyclic-feedback-families.md)

`class_nontrivial_of_stable_pair` uses structural coarseness to show
that a distinct slot paired with the actual carried return by any
stable refinement of the entry classes also belongs to its normalized
class. Whether it can replace the return depends on its completed-header
key. `optimize_arrives_iff` preserves every header arrival's predecessor
occurrence, count and complete register bank. `optimize_run_eq` preserves
every native CFG block-budget result, including absence at that budget,
for the original input bank.
[Structural coarseness](sea-of-nodes-gvn-cyclic-feedback-discovery.md)

```lean
module
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Thms

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort)
open GVN.Cyclic.TwoBackedges.Family.Discovery.Return
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Program)

example {regs : List (ValueSort Unit)} (p : Program Opcode regs word)
    (input : Bank (regs := regs) model) (fuel : Nat) :
    (optimize p).source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input :=
  optimize_run_eq p fuel input
```

The mutual-family fixture returns the later carried slot. The policy
redirects it to the earlier slot, retaining the full banks on both
selected feedback edges. At the common returning budget, the true
route returns `7` and the false route returns the wrapping word for
`−1`. Reversing one false-edge subtraction makes the returned slot
a singleton, so the policy keeps its original wire. The regressions
also cover an already canonical result, a header-produced result, and
an earlier same-class slot overwritten with a different exit key.
[Native regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Regression.lean)

```sh
topic=SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family
make check CHECK_TARGETS="+Silmaril.$topic.Discovery.Return.Thms +Silmaril.Proofs.$topic.Regression"
lake env leanchecker "Silmaril.$topic.Discovery.Return.Thms"
lake env leanchecker "Silmaril.Proofs.$topic.Regression"
```

Click PLDI ’95 §3.1 step 3 motivates replacing a redundant use with a
representative. The admitted profile is a direct carried-word return
in this native two-feedback graph, with structural entry and feedback
keys and a checked post-header use. Producer deletion and completeness
for semantic equality are separate.
[Pinned PLDI paper](sea-of-nodes-gvn-cyclic-pass.md#sources) ·
[Pinned dissertation](sea-of-nodes-gvn-cyclic.md#sources)
