# Least ordered packet projection for the typed loop exit

`Projection.rewriteScanned?` takes an ordered, typed projection and the
actual full-packet exit block. It runs the existing backward demand scan
and invokes the same exit rewriter as the compactor on the surviving
slice. Extra packet slots are allowed. The compactor separately checks
that every forwarded slot is used in its final artifact.
[Definitions][defs] · [Compaction][compact]

`Projection.rewriteScanned?_iff` characterizes success for a scanned
pure, straight-line returning exit. Every index in the computed
demand set that names an old packet slot must be retained, and retaining
all those slots suffices for the checked rewrite. Ambient function
inputs follow the packet and stay available under every projection.
The proof relates indexed operand reads to the domain of the actual
partial typed rename. It tracks that domain under retained and removed
lets and through the return, using the list of reads that the backward
scan carries across each let. [Theorems][thms]

`Emission.minimal_projection` states the result for a concrete compacted
CFG by slot inclusion. `Emission.rewriteScanned?_exact` replays the exact
exit code of that CFG when supplied its computed projection. Click's
Schedule Late (§2.3) locates a Φ read at the corresponding incoming
edge. This result determines which old slots the exiting edge must
deliver after the moved code has been fixed. The criterion concerns
syntactic return dependencies and ordered typed projections of the
same surviving slice. It leaves value equality, alternate code, and
recomputation outside the profile. [Click PLDI ’95][paper] · [Theorems][thms]

The runnable fixture uses the full-packet exit from the discovered
interleaved move. The rewrite accepts `[4, 6, 8]` and its strict superset
`[0, 4, 6, 8]`. It rejects `[6, 8]` because the first moved producer reads
slot 4 and the exit return depends on that producer. The regression
also rewrites a return that reads only an ambient input with an empty
packet. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Regression
cat >/tmp/gcm-exit-projection-minimality-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Example
#eval observe
#eval ambientOnly
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-exit-projection-minimality-example.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Minimality.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[compact]: sea-of-nodes-gcm-compact-exit.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Minimality/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Minimality/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Minimality/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Minimality/Regression.lean
