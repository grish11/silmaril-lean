# Simultaneous cyclic GVN for two native feedback occurrences

The single-pair checker uses the existing native
`Quads.Loop.Tail.TwoBackedges.Program`. The family checker accepts a list
of nominated typed word-slot equations and a replacement return slot
in that same program.
[Single-pair checker and native model](sea-of-nodes-gvn-cyclic-two-backedges.md) ·
[Family definitions](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Defs.lean)

The preheader check starts with independent typed argument keys. The
header check starts from one seed for the entire family. Merging a
pair joins its current classes, so overlapping nominations share a
key transitively. `seed_matches` proves that every nominated pair has
the same key in the resulting seed. Each feedback check runs the
ordered header and its own actual feedback block using that common
seed, then checks every equation on the resulting bank. The same
post-header keys check the return operand. Word keys retain exact
operand order, and both occurrences are checked independently of
the predicate values.
[Word value numbers](../../Silmaril/SSA/SeaOfNodes/GVN/WordNumber/Defs.lean)

`certify?` returns a `Certificate` with separate evidence for the
preheader, each feedback occurrence, and the return use.
`Certificate.invariant` proves that the whole family holds at entry
and survives any selected feedback. `Certificate.arrives` applies it
to a particular native header arrival. `rewrite?` changes only the
actual return operand. `rewrite_step_eq` preserves the selected
occurrence and its complete feedback bank or the returned word for
every bank satisfying the family. `rewrite_step_of_arrives` supplies
that condition at each actual arrival. `rewrite_run_eq` and its corollaries
preserve every common-budget result, finite returns and absence from
the original typed input.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Thms.lean)

```lean
module
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Thms

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort)
open GVN.Cyclic.TwoBackedges (WordSlot)
open GVN.Cyclic.TwoBackedges.Family
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Incoming Program)

example {regs : List (ValueSort Unit)} {p : Program Opcode regs word}
    {equations : Equations regs} {replacement : WordSlot regs}
    (cert : Certificate p equations replacement)
    {input old : Bank (regs := regs) model} {via : Incoming} {count : Nat}
    (arrived : p.Arrives model input via count old) : Holds equations old :=
  cert.arrives arrived

example {regs : List (ValueSort Unit)} (source target : Program Opcode regs word)
    (equations : Equations regs) (replacement : WordSlot regs) (input : Bank (regs := regs) model)
    (admitted : rewrite? source equations replacement = some target) (fuel : Nat) :
    target.source.runFrom model fuel 0 input = source.source.runFrom model fuel 0 input :=
  rewrite_run_eq admitted fuel input
```

In the fixture, the next values of the first pair read the current
second pair. The next values of the second pair use earlier header
computations from the current first pair. Each pair alone fails its
feedback check, while the simultaneous certificate accepts both.
After a taken backedge the original and rewritten programs return
`11` on the true route and `3` on the false route. Reversing the operands
of a single subtraction rejects the false occurrence, even though
the other equation there still checks. Forcing that rejected
redirect would return `5` on that route. A separate seed check joins
overlapping nominations.
[Executable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Regression.lean)

```sh
topic=SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges
make check CHECK_TARGETS="+Silmaril.$topic.Family.Thms +Silmaril.Proofs.$topic.Family.Regression +Silmaril.Proofs.$topic.Regression"
lake env leanchecker "Silmaril.$topic.Family.Thms"
lake env leanchecker "Silmaril.Proofs.$topic.Family.Regression"
```

Click's dissertation §§4.1–4.2 motivates checking corresponding cyclic
inputs in occurrence order. PLDI ’95 §3.1 step 3 motivates using a
representative at a redundant use. Here the caller supplies the family
and the typed return use. The executable checker verifies that family
as an invariant of the existing native program. Automatic cyclic
class discovery, producer removal and backend emission remain separate.
[Pinned dissertation](sea-of-nodes-gvn-cyclic.md#sources) ·
[Pinned PLDI paper](sea-of-nodes-gvn-cyclic-pass.md#sources)
