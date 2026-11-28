# Compact the live-in packet of an emitted loop exit

`ExitSink.Compact.compact?` takes the actual full-packet typed CFG,
including the output of automatic partition discovery. It scans the
exit from its return values through the typed operands of live lets,
using the same backward binding transfer as discovery. The projection
keeps demanded packet slots in their original order. Function inputs
already in scope remain available. An exit with a non-return terminator
is refused. [Definitions][defs] · [Partition discovery][discovery]

The pass applies the projection to the actual edge argument list and
rewrites the live exit operands and return references at their new
typed positions. Dead pure exit lets are dropped. Each surviving
operand must translate to a variable of its original type, so a
projection that drops a needed slot is refused by the exit rewriter.
The pass re-reads the emitted exit and checks that every forwarded
slot is needed by its return dependency closure. `packet_indices`
specifies the selected old slots and `packet_used` certifies the
absence of unused projected slots. [Theorems][thms]

`header_packets` retains each exact successor occurrence and its packet
order. The true feedback edge keeps its packet, and the false edge
passes the ordered projection of its old packet. `false_target` and
`false_occurrence` relate the new destination and argument reads to
the original false slot and header terminator cut. `run_eq` and
`denotePart` compare the full-packet and compact CFGs at common block
fuel and in partial denotation. The control rewrite keeps the
existing blocks, so it needs no fuel offset. [Theorems][thms]

The source connection is Click's placement of Φ uses on the matching
incoming edge (§2.3). Compaction changes which values that edge
delivers after late placement. The scope covers a pure total,
straight-line returning exit and the existing saved-loop label family.
It follows syntactic return dependencies. Deduplicating equal values
and replacing a forwarded copy by an ambient input are outside the
profile. [Click PLDI ’95][paper]

The lowered interleaved example discovers the moved chain and then
reduces the false packet from nine words to old slots `[4, 6, 8]`.
The chain's first producer reads slots 6 and 4 in that order, while
the packet itself keeps original slot order. Feedback stays
`[3, 2, 7]` and both CFGs return 9 at fuel 5 after two feedbacks.
A second input gives distinct values `[2, 4, 1]` in projected order.
The regression also refuses a projection that drops all packet slots
and verifies that a dead let's read of old slot zero leaves that slot
omitted. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Regression
cat >/tmp/gcm-compact-exit-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Example
#eval observe
#eval refusesMissingOperand
#eval prunesDeadRead
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-compact-exit-example.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Compact.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[discovery]: sea-of-nodes-gcm-loop-exit-discovery.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Compact/Regression.lean
