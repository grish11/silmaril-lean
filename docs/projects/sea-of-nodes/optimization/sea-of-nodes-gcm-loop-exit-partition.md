# Sink a noncontiguous set from the saved loop header

`ExitSink.Partition.sink?` takes the actual saved-loop CFG and one bit for
each binding in its current header. A true bit moves the binding to the
exit. The bits stay in input-header coordinates throughout the pass.
`operation_order` proves that the emitted header and exit contain the two
indicated subsequences of the original typed operation order.
[Definitions][defs] · [Theorems][thms]

The pass scans the mask from left to right. Each retained binding crosses
the preceding moved bindings using the existing checked adjacent swap.
A swap rejects a read of the crossed producer. The typed remapping
updates the remaining operand references and both branch argument
packets. Once the moved bindings form a suffix, the existing suffix
emitter checks the guard and feedback against the retained scope and
requires the false-edge return to read a moved result. It rechecks the
moved bindings' use and operand sites on the actual emitted exit using
exact dominance and within-block availability. A rejection
at any step returns no program. [Typed swap][swap] · [Suffix emitter][suffix]

`operand_occurrence` resolves each retained-scope argument on the
actual false edge at the end of the retained header. `header_packets`
compares both outgoing occurrences, including the untaken one. The true
edge keeps the original feedback bank, and evaluating the new false
packet in dependency order yields the old exit result. `run_eq` covers
returns and exhaustion at common block fuel, and `denotePart` covers
partial denotation. The rewrite keeps the original exit block, so the
fuel comparison has no offset. [Theorems][thms]

Click's Schedule Late (§2.3) locates Φ uses in their corresponding
predecessor blocks. Here the transformation changes the false-edge
packet and moves the nominated computation and its internal reads to the
existing exit. The supported shape remains a pure, total saved loop with
one true-edge self-latch and one immediate false-edge return. The caller
supplies the move set. The exit packet carries the full retained scope,
and the scope permits unused pure lets in the moved set.
[Click PLDI ’95][paper] · [Coverage ledger][coverage] · [Schedule Late bound][late]

The runnable fixture prepares a typed lowered header in origin order
`[3, 5, 0, 6, 4, 7]`. It moves `[5, 6, 7]` while retaining `[3, 0, 4]`.
The second moved binding reads the first, and the third reads both.
Origin 4 still supplies feedback. The true edge carries `[3, 2, 7]`,
and both programs return 9 at fuel 5 after two feedbacks. Other
fixtures refuse a retained consumer of a moved value, a moved guard,
and a moved feedback value. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Regression
cat >/tmp/gcm-exit-partition-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Example
#eval observe
#eval refusesRetainedRead
#eval refusesGuard
#eval refusesFeedback
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-exit-partition-example.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Partition.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[late]: sea-of-nodes-gcm-late-placement.md
[suffix]: sea-of-nodes-gcm-loop-exit-suffix.md
[swap]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Thms.lean
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Partition/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Partition/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Partition/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Partition/Regression.lean
