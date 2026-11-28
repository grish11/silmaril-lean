# Applying a checked sequence of loop-header placements

Click's PLDI ’95 §§2.2–2.4 constrain placements by definitions and uses,
including Φ operands on their incoming CFG edges. Section 2.4 notes
that placing one instruction can change the latest legal position of
another. This slice checks a finite explicit schedule one request at a
time in the existing typed single-latch header.
[Proceedings][paper] · [Archived PDF][pdf] · [Checked pair][pair]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
`Header.Sequence.schedule?` takes a list of the existing `Pair.Request`
values. Every binding index and pre-removal cut belongs to the CFG
immediately before that request. The single-step emitter resolves and
checks the binding's operand origins, ordinary reads and Φ occurrence
slots on that CFG, then applies the existing earlier or later motion.
The automatic chooser and pair serve their existing entry points.
[Definitions][defs] · [Corridor chooser][corridor]

Original binding identities start as the input header's zero-based
indices. The executable state keeps them in current binding order and
removes and reinserts the selected original index at exactly the
emitter's translated index. It checks the selected identity against the
history before emitting. A previously moved binding is refused even if
it has a different current index. The sequence returns only its final
CFG. A failed check or repeated identity yields `none`.
[Definitions][defs]

`move?_transport` connects the identity splice to the typed emitter's
operation order. `run?_tracked` proves that the current origins
permute the source indices, align with the emitted operation symbols
and type signatures, and have distinct moved identities in the
history. `schedule?_refuses_suffix` covers failure after any accepted
prefix. The single-step semantic law composes to preserve exact
feedback and exit tuples, every CFG fuel result, native backedge
budgets at fuel `budget + 3`, and partial denotation. This covers
finite explicit schedules of distinct pure total bindings in one
header. [Theorem header][thms]

The example moves the addition later, brings the comparison to the
front, then moves the second multiply later. It reports final origins
`[3, 1, 0, 2]` and moved identities `[0, 3, 2]` in request order.
The alternative third request selects the addition at current index
3, where the individual emitter could move it again. The sequence
refuses because that binding's original identity is 0, already moved
by the first request. The regression also checks current-read
refusal, exact successor arguments, and zero and two backedges.
[Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Example.Defs
cat >/tmp/gcm-header-sequence-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Example
#eval observe accepted
-- some (["ult", "muli", "addi", "muli"], [3, 1, 0, 2], [0, 3, 2], [none, none, some 32])
#eval observe repeated
-- none
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-header-sequence-example.lean

make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Pair.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[pair]: sea-of-nodes-gcm-header-pair.md
[corridor]: sea-of-nodes-gcm-corridor-placement.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Sequence/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Sequence/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Sequence/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Sequence/Regression.lean
