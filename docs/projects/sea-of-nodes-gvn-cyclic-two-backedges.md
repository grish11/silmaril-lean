# Checked cyclic GVN on two native feedback occurrences

The coverage ledger's loop model distinguishes the arriving predecessor
and the complete bank that it supplies. The existing preheader-seeded
GVN driver works on the single-backedge `Loop.Graph`. This checker uses
the native `Quads.Loop.Tail.TwoBackedges.Program` with one preheader, one
header, and two distinct feedback blocks entering that header.
[Coverage ledger](sea-of-nodes/coverage.md) ·
[Single-backedge driver](sea-of-nodes-gvn-cyclic-preheader-iteration.md) ·
[Native two-feedback program](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/Defs.lean)

Nominate a pair of carried word slots and a replacement word slot for
the return. The checker assigns structural keys to exact typed argument
positions and uses the existing word numbering for literals and ordered
arithmetic. It runs the existing ordered quad evaluator on these keys.
The preheader starts with independent argument keys. At the header,
only the two nominated slots share a key. The checker runs the header
followed by each actual feedback block separately and requires that each
block's final bank again gives the pair matching keys. The exit test
compares the original and replacement reads from the completed header
bank. Predicate operations cannot supply operand values to a word
producer in the admitted signature. The checker ignores predicate
values and checks both occurrences, including one that could be
unreachable on a particular input.
[Checker](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Defs.lean) ·
[Word keys](../../Silmaril/SSA/SeaOfNodes/GVN/WordNumber/Defs.lean) ·
[Native opcode profile](../../Silmaril/SSA/SeaOfNodes/Pure/ConstantFold/Comparison/Defs.lean)

`arrives_eq` proves the nominated pair equal at every actual header
arrival. If `rewrite?` returns a program, that program changes only the
post-header return operand. `rewrite_step_eq` preserves the selected
feedback occurrence with its full bank, or the returned word.
`rewrite_run_eq` lifts that invariant to the native CFG's block-budget
execution on the original input bank. Existential finite returns and
absence at every finite budget follow.
[Public theorems](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Thms.lean)

```lean
module
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Thms

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort)
open GVN.Cyclic.TwoBackedges
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Program)

example {regs : List (ValueSort Unit)} (source target : Program Opcode regs word)
    (a b replacement : WordSlot regs) (input : Bank (regs := regs) model)
    (admitted : rewrite? source a b replacement = some target) (fuel : Nat) :
    target.source.runFrom model fuel 0 input = source.source.runFrom model fuel 0 input :=
  rewrite_run_eq admitted fuel input
```

The fixture computes separate preheader producers for the nominated pair
and separate return producers that read each carried slot. Choosing the
add feedback gives packet words `(14, 14)` and return `17`. Choosing the
subtract feedback gives packet words `(6, 6)` and return `9`. Both
original and rewritten programs execute the selected feedback and return
from the next header. The wraparound check uses the maximum `i64` bit
pattern and observes zero in the carried slots on the add feedback.
Reversing a subtraction on only the false occurrence refuses the edit
even though the preheader, true occurrence, and conditional exit match.
Forcing that rejected redirect would change the false-route return
from `9` to the word encoding `-3`.
[Executable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Regression.lean)

```sh
topic=SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges
make check CHECK_TARGETS="+Silmaril.$topic.Thms +Silmaril.Proofs.$topic.Regression"
lake env leanchecker "Silmaril.$topic.Thms"
lake env leanchecker "Silmaril.Proofs.$topic.Regression"
```

Click's dissertation §§4.1–4.2 motivate preserving input order when
checking cyclic congruence. Each arriving edge supplies a distinct
operand occurrence for every carried slot. PLDI ’95 §3.1 step 3
motivates replacing uses of a redundant value. This slice checks one
proposed carried equality and one return use. Class discovery or
refinement across multiple carried equalities, producer deletion,
schedule reconstruction, and backend lowering are separate obligations.
[Pinned dissertation](sea-of-nodes-gvn-cyclic.md#sources) ·
[Pinned PLDI paper](sea-of-nodes-gvn-cyclic-pass.md#sources)
