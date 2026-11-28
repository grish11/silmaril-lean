# Diagnosing the first guarded SCCP admission

`FIFOAdmission.diagnose map seed` uses the guarded capture compiler's
write check and typed fact intersection. If both succeed, it runs the
same finite typed FIFO used by the guarded singleton dispatcher.
On refusal it returns the actual run, with its final typed bank,
occurrence marks, visit sequence, and pending queue, alongside the
transported entry facts and the post-header continuation and selector
facts. `inspect_row` verifies these fields and the empty pending queue.
A refused row has both or neither feedback occurrence marked.

`diagnose_compile` recovers the actual compiler outcome after erasing the
extra diagnostic fields and mapping successful emissions to unit.
`compile_checker_iff` spells out the exact compiler refusal condition.
An aliased write and an inconsistent fact intersection stop before the
FIFO and have their own cases. Concrete entry inputs are handled by the
emitted guard on successful compilation.

## Why a read-only suffix cannot rescue this refusal

The analysis uses the optimistic flat order. A successful fact
intersection is at least as precise at every original port when read
back through the typed map. With singleton written fibres, pulling
back an abstract block gives the original ordered abstract writes.
Inducting through the bounded simultaneous transfer bounds each carried
fact read through the map by its counterpart in the original fixed row,
and bounds the target occurrence marks by inclusion. FIFO agreement with
the simultaneous solver transfers that inclusion to the actual checker.

An admitted seed therefore cannot acquire a second marked feedback
occurrence through checked capture transport. A first checker refusal
from that seed must be `neitherMarked`. If the suffix passes the write
check on the transported program, the direct compiler reports
`neitherMarked` for a successful final intersection and
`incompatibleFacts` when the final intersection fails. This uses the
exact composition of the program transport and fact intersection.
The suffix hypothesis checks the intermediate bank, including spare
intermediate slots. [Write admission](rice-loop-sccp-write-admission.md) ·
[Exact fact transport](rice-loop-sccp-exact-fact-transport.md)

The fixture changes the two operands of the header's unsigned
comparison to the same port. The continuation fact becomes false, so
the drained row marks entry and exit. The suffix identifies the spare
right operand slot with the read-only left operand slot. All three
structural checks pass, and both compiler calls refuse with
`neitherMarked`.

## Run the example

Save the following as a Lean file and run `lake env lean <file>`.

```lean
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.TwoBackedges.ContextEmbedding.FIFOAdmission
open Example (writeChecks summary outcomes invalidCases)

#check diagnose
#check inspect_row
#check direct_of_neither

#eval writeChecks
-- First, second, and composite checks are all true.
#eval summary
-- Continuation is false and selector is true.
-- Entry and exit are marked. Nine jobs visited and zero pending.
#eval outcomes
-- First and direct compiler both refuse with checker neitherMarked.
#eval invalidCases
-- The structural and intersection cases report aliasedWrite and incompatibleFacts.
```

[Public API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/FIFOAdmission/Thms.lean) ·
[Checked regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/TwoBackedges/ContextEmbedding/FIFOAdmission/Regression.lean)
