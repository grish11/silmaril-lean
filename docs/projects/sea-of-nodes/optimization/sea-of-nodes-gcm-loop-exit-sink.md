# Sink an exit-only producer in the saved single-latch CFG

`ExitSink.sink?` takes the actual saved-loop typed CFG and a zero-based
current header binding index. It checks that entry jumps to the header,
that the nominated producer is the final header let, and that its result
has exactly one read. That read must be argument zero of the header's
false edge into the exit, which must immediately return it. The true edge
feeds the saved and carried bank back to the header. The checker rejects
a read of the producer in the guard or in any feedback argument.
[Definitions][defs] · [Theorems][thms]

The emitter removes the nominated let and keeps the header's earlier lets.
It replaces the false-edge result argument with the operation's typed
operand packet in source operand order. The existing exit block evaluates
the operation at cut zero and returns its result at cut one. All operands
are in scope on that exact edge even when they read header-local values.
The emitted CFG passes the existing dominance and local cut checker.
`source_occurrence` resolves the old Φ read at the original header
terminator. `operand_occurrence` resolves each new exit argument on the
same false edge at the shortened header's terminator. `packetRefs_eval`
connects those arguments to the actual operand reads in the exit block.
[Theorems][thms]

Click's Schedule Late (§2.3) locates an existing Φ use in its predecessor.
Here the old use therefore pins the original value to the header under
a fixed use inventory. This rewrite changes that inventory by transporting
the operands and replacing the result's Φ read with an ordinary return
read in the exit. The scope is one pure total operation, one self-latch
with true feedback, and one immediate returning exit. The output has the
same blocks and slots, with a retyped exit signature. Switches, multiple
exits, other consumers, and pass-wide placement ranking are outside this
profile. [Click PLDI ’95][paper] · [Coverage ledger][coverage] · [Schedule Late bound][late]

`entry_packet` preserves the entry bank. `header_packets` compares both
outgoing occurrences even when the guard takes only one of them. The
feedback packet is identical, and evaluating the new exit packet reproduces
the old result. Because the pass reuses the old exit block, no fuel offset
is needed. `run_eq` and `denotePart` prove equal returns and exhaustion
at each common block-fuel budget and equality of the partial denotation.
[Theorems][thms]

The lowered regression moves origin 7's add into the exit, keeps the true
packet `[3, 2, 7]`, and changes the false packet from `[9]` to `[5, 4]`.
Both programs exhaust at fuel 4 and return 9 at fuel 5 after two feedbacks.
The refusal fixture makes the same add a true-edge feedback operand while
retaining the false-edge result read. [Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Regression
cat >/tmp/gcm-loop-exit-sink.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Example
#eval observe
#eval refusesFeedback
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-loop-exit-sink.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.ExitSink.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[late]: sea-of-nodes-gcm-late-placement.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/ExitSink/Regression.lean
