# Re-analyze the compacted loop exit

`Emission.rescan` applies the existing executable demand scan to the actual
compacted exit. The new scan demands every compact packet position and
retains every surviving let. A demanded ambient input can still appear
after the in-packet positions. Its numeric position is interpreted in
the compact scope. [Theorems][thms] · [Compaction][compact]

The proof follows the actual partial typed rename through the exit rewrite.
Under a kept binding it transports the required local and older reads.
Under a removed binding it transports reads back to the preceding scope.
The emitted-exit coverage check then supplies demand for every forwarded
slot. `Projection.keepAll_indices` gives the precise new packet projection
as `List.range` of its arity. [Theorems][thms]

`Emission.compact_again` calls `compact?` on the first emission's CFG.
It proves that the existing implementation succeeds with the identity
projection, the same typed exit code, and the same exact packets at
both header occurrences. The comparisons use heterogeneous equality
across the propositionally equal packet signatures.
`Projection.keepAll_types` gives that signature equality. The ordinary
compaction observation laws apply to the second result as well.
[Theorems][thms] · [Projection minimality][minimality]

The proof concerns syntactic demand and exact rewriting for pure
straight-line returning exits in the saved-loop label family. The edge
argument reasoning follows Click's use of the exact incoming occurrence
for Φ reads (§2.3). [Click PLDI ’95][paper]

The lowered interleaved example runs both compactions. The first selects
old slots `[4, 6, 8]`. The second scan reports reads `[2, 1, 0]` in the
compact scope and projects `[0, 1, 2]`. The three moved lets and return
retain their operand indices. Feedback is `[3, 2, 9]` and the false edge
carries the same ordered packet `[2, 4, 1]` on both passes. The ambient-only
example forwards nothing on either pass, even though the second scan
reports the ambient read at position zero. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Regression
cat >/tmp/gcm-compaction-stability-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Example
#eval observe
#eval ambientOnly
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-compaction-stability-example.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Stability.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[compact]: sea-of-nodes-gcm-compact-exit.md
[minimality]: sea-of-nodes-gcm-exit-projection-minimality.md
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Stability/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Stability/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Stability/Regression.lean
