# Read explicit Φ rows from the compacted loop exit

`Phi.rowAt?` reads typed operands from the actual emitted CF entry or
header terminator. It checks the exact jump, true, or false slot before
checking the destination. The row retains its terminal scope and operand
order. This implements the incoming-occurrence rule for Φ reads in
Click's Schedule Late (§2.3). [Definitions][defs] · [Click PLDI ’95][paper]

`Phi.view` presents these rows to the existing positional `PhiView`.
Each checked CF predecessor and slot gives a source index, and local
label zero denotes the exit. `Phi.latchAt_packet` identifies each
positional latch with the typed packet read through the existing CF
occurrence evaluator. `Phi.Incoming.transfer_iff` gives the corresponding
λSSA branch transfer. The view covers exit arrivals in the compactable
saved-loop label family. CF still supplies branch selection and full
program execution. [Theorems][thms] · [Explicit Φ API][phi]

`Phi.rowAt_project` and `Phi.packetAt_project` compare extraction before
and after compaction using the emitter's typed ordered projection.
`Phi.compact_rows_again` runs the same compactor on the emitted CFG and
preserves all extracted rows, evaluated packets, and packed Φ values.
The row and packet statements use heterogeneous equality across the
propositionally equal signatures. Common-fuel and partial observation
laws continue to come from the existing compactor. [Theorems][thms] · [Compaction][compact] · [Stability][stability]

The interleaved moved-producer fixture selects old slots `[4, 6, 8]` and
latches `[2, 4, 1]` before and after recompaction. The ambient-only exit
latches unit, while the feedback slot has no exit row. A CF fixture in the
same label family sends both header branches to the exit. They latch
different values, `[7]` and `[9]`, and the actual CF runs return those
values under the corresponding guards. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Regression
cat >/tmp/gcm-compact-exit-phi.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Example
#eval interleaved
#eval ambientOnly
#eval parallel
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-compact-exit-phi.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Phi.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[compact]: sea-of-nodes-gcm-compact-exit.md
[stability]: sea-of-nodes-gcm-exit-compaction-stability.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Phi/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Phi/Thms.lean
[phi]: ../../../../Silmaril/SSA/PhiView/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Phi/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Phi/Regression.lean
