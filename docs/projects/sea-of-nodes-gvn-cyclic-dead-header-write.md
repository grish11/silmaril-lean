# Checked header deletion after native cyclic GVN

`afterReturn? p index` runs the automatic carried-return pass and checks
one nominated header assignment in the program it emits. An accepted
deletion removes exactly that assignment and keeps the order of all
surviving quads. The typed register bank, preheader, branch ports and
both feedback blocks stay as they were in the redirected program.
[Executable checker](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Discovery/Return/Deletion/Defs.lean) ·
[Automatic return redirect](sea-of-nodes-gvn-cyclic-automatic-return.md)

The check follows the nominated write's value through the actual
header suffix. Each surviving quad reads its operands before it writes
its destination. The check therefore rejects a read of the old value,
including an operand of the first instruction that overwrites it. An
overwrite ends the check because later reads use that new definition.
If the old value reaches the header terminator, the continuation test,
selector and return must read other slots. Both feedback blocks must
then overwrite the nominated slot before reading it or passing the
complete bank back to the header. Each block is checked independently.

The acyclic producer eraser checks ordered SSA operands and an explicit
outgoing packet. The native quad checker uses the existing register
reads and writes to distinguish successive definitions of one slot.
The proof shows that skipping a write can change only its destination
until the first overwrite. Checked feedback overwrites restore equality
of the complete banks. The native step theorem therefore preserves the
selected occurrence and packet or the returned word. The composition
theorems preserve all labelled header arrivals and every native CFG
block-budget result from the original input bank.
[Acyclic deletion](../../Silmaril/SSA/SeaOfNodes/Pure/Deletion/Thms.lean) ·
[Native deletion and composition laws](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Discovery/Return/Deletion/Thms.lean)

```lean
module
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Thms

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort)
open GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Program)

example {regs : List (ValueSort Unit)} (p emitted : Program Opcode regs word)
    (index fuel : Nat) (input : Bank (regs := regs) model)
    (accepted : afterReturn? p index = some emitted) :
    emitted.source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input :=
  afterReturn?_run_eq accepted fuel input
```

The unchanged mutual-family fixture still reads the second header
assignment on both feedback edges after redirection. In the admitted
variant each feedback block already recomputes that scratch value
before its first read. The pipeline redirects the carried return and
reduces the header from two assignments to one while preserving both
complete feedback packets. Delaying the false edge's recomputation
leaves an earlier read and causes refusal. The packet-only fixture
also refuses an omitted overwrite on the false edge, where the slot
has no instruction use and remains observable in its outgoing bank.
[Native regressions](../../Silmaril/Proofs/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Regression.lean)

## Automatic cleanup

`Deletion.Cleanup.optimize p` first redirects the carried return, then scans the
actual emitted header in increasing index order. It removes the first write
accepted by the same checked deletion test and starts a fresh scan on the
residual program. Each success removes one write, so the redirected header's
binding count is enough fuel. At the end, every remaining index fails this
specific check. The test still requires an overwrite before any surviving
read or full-packet export. [Discovery and cleanup laws](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/TwoBackedges/Family/Discovery/Return/Deletion/Cleanup/Thms.lean)

The three-write fixture first removes index 1. That removal eliminates the
only read of the temporary value at index 0 and exposes the second deletion.
The last write remains live through feedback. The actual execution yields the
same complete packets and returns on both routes. Discovery finds no
candidate in either of the existing false-edge refusal fixtures.

```lean
module
import Silmaril.SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup.Thms

open Silmaril.SSA.SeaOfNodes
open Diamond (ValueSort)
open GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion (check)
open GVN.Cyclic.TwoBackedges.Family.Discovery.Return.Deletion.Cleanup
open Pure.SubZero (word)
open Pure.ConstantFold.Comparison (Opcode model)
open Quads.Loop.Blocks (Bank)
open Quads.Loop.Tail.TwoBackedges (Program)

example {regs : List (ValueSort Unit)} (p : Program Opcode regs word)
    (fuel : Nat) (input : Bank (regs := regs) model) :
    (optimize p).source.runFrom model fuel 0 input = p.source.runFrom model fuel 0 input ∧
      (∀ index < (optimize p).header.length, check (optimize p) index = false) :=
  ⟨optimize_run_eq p fuel input, optimize_saturated p⟩
```

```sh
topic=SSA.SeaOfNodes.GVN.Cyclic.TwoBackedges.Family
make check CHECK_TARGETS="+Silmaril.$topic.Discovery.Return.Deletion.Cleanup.Thms +Silmaril.Proofs.$topic.Regression"
lake env leanchecker "Silmaril.$topic.Discovery.Return.Deletion.Cleanup.Thms"
lake env leanchecker "Silmaril.Proofs.$topic.Regression"
```

Click PLDI ’95 §3.1 step 3 motivates the preceding use redirection.
The checked erasure here is local IR cleanup. The old carried slot
remains in the bank, and its entry and feedback definitions can still
be observed in complete packets. Dropping such a slot would require
a projection simulation for both feedback occurrences and the
retained header and return reads.
[Pinned PLDI paper](sea-of-nodes-gvn-cyclic-pass.md#sources) ·
[Existing single-backedge projection laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Blocks/Prune/Thms.lean)
