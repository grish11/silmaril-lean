# Exact guarded SCCP fact transport under composition

`FactTransport.pushFacts_comp` equates the actual one-shot and staged
intersections for any two sort-preserving port maps in the pure guarded
five-block profile.

```text
pushFacts (thenMap first second) facts =
  (pushFacts first facts).bind (pushFacts second)
```

Both maps may identify ports. The result is the same typed fact tuple on
success or `none` on both paths. The fact law concerns maps and contracts
alone. It applies before any program write checks or FIFO admission.

`pushFacts_compatible_iff` characterizes success. Every old coordinate
must be above bottom, and any constants in one target fibre must agree.
Overdefined facts impose no constraint. `pushFacts_unused` gives an
overdefined fact at each target port with an empty fibre. This also
explains why a spare intermediate slot contributes no constraint if the
second map identifies it with a used port.

The earlier composition theorem gave equality of coverage at every final
valuation. A successful intersection has a covered valuation, and a
covered valuation lets us probe each coordinate by varying it alone.
Boolean and positive-width word carriers have at least two values, so
each constant can be distinguished from an overdefined fact. This
recovers equality of the actual fact tuples.
[Public laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/FactTransport/Thms.lean) ·
[Earlier coverage comparison](rice-loop-sccp-port-composition.md)

## From first admission to the final compiler

Supply an actual successful first compilation. `final_inputs_eq` equates
the two final typed programs, including every renamed read, write and
terminator, together with the optional fact blocks. `final_fifo_eq`
therefore equates the full drained FIFO states whenever a final fact
block exists. The compiler runs that FIFO only after its structural and
intersection checks pass.

With a successful second write check, `second_compile_eq` equates the
complete second and one-shot compiler results, including actual emitted
artifacts. `second_compile_check` gives the staged write-alias refusal on
the other branch, and `compared_eq` identifies the final artifacts stored
in an existing successful comparison.

These are final-call laws after first admission. In the noninjective
admission fixture the first compiler admits true feedback, then both final
calls refuse with `neitherMarked`. The first admission certificate
describes the intermediate facts and FIFO row. The final checker recomputes
its row under the intersected facts.
[Noninjective admission fixture](rice-loop-sccp-noninjective-admission.md)

The second write check is essential to the compiler equality. The new
boundary fixture identifies a spare intermediate port with a written
output. The stagewise checker sees both preimages and refuses
`second aliasedWrite`. The composite write check sees just the written old
port, and the direct compiler emits an artifact.

## Run the regressions

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport
  (pushFacts_comp final_inputs_eq final_fifo_eq second_compile_eq)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FactTransport.Example
  (conflict unusedDefault unsafeWrites unsafeOutcomes)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.LiftComposition.Example
  (run)

#check pushFacts_comp
#check final_inputs_eq
#check final_fifo_eq
#check second_compile_eq
#eval conflict
-- (true, false, false) for first, staged-final, and one-shot fact success
#eval unusedDefault
-- some overdefined at the final interior i16 port
#eval unsafeWrites
-- (true, false, true) for first, second, and composite write checks
#eval unsafeOutcomes
-- First and one-shot select true. Staged refuses at the second write check.
#eval (run 65535 true, run 0 false)
-- Intermediate, staged, and direct CF and numbered artifacts return 99 and 14 respectively.
```

[Checked regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/FactTransport/Regression.lean)
