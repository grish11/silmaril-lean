# Scheduling loop-header bindings by original identity

Click's PLDI ’95 §§2.2–2.4 constrain placements by definitions and uses,
with Φ operands read on incoming CFG edges. Section 2.4 notes that
placing one instruction can change the legal placement of another.
This scheduler resolves and checks each priority on the current typed
single-latch header. [Proceedings][paper] · [Archived PDF][pdf] ·
[Checked explicit sequence][sequence]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.
`Header.Priority.schedule?` accepts a list of distinct original binding
indices and processes them in that order. It finds each identity in
the current origin list, then tries every strictly earlier header cut
in increasing cut order. The first cut that the existing checked
sequence step emits wins. Lower local index is the only improvement
criterion. The step checks actual operand sites, ordinary reads and Φ
occurrences, then emits the typed move and updates the origin order.
[Definitions][defs]

When every earlier cut fails, the scheduler leaves that binding in
place for this visit and adds no request. Unknown or duplicate
identities yield `none`. The profile is greedy earlier motion of pure
total bindings within one header, with each priority visited once.
The existing automatic corridor chooser still serves its block
placement and ranking API. [Definitions][defs] · [Corridor chooser][corridor]

`resolve?_sound` identifies the original binding at the returned
current position. `choose?_earliest` and `choose?_eq_none` characterize
the search over the finite earlier cuts accepted by the existing
checker and emitter. `schedule?_exists` guarantees a result for
in-range, distinct priorities, including an empty plan if every
priority is skipped. `schedule?_replay` proves that replaying the
returned `Pair.Request` list with `Header.Sequence.schedule?` yields
the exact returned CFG. Its proofs give equal feedback and exit
tuples, CFG results at all fuels, native backedge budgets at fuel
`budget + 3`, and partial denotation. [Theorem header][thms]

Priority list `[3, 2, 1]` first moves the comparison to the front.
Original binding 2, the exit multiply, is then at index 3. Stale index
2 names the feedback multiply. Its operand from the preceding addition
is first available at cut 2, so searching earlier cuts at stale index
2 fails. The second request moves the exit multiply, and the final
priority is skipped. The two emitted requests both read `(3, 0)`
because they are interpreted in their respective current headers.
[Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Example.Defs
cat >/tmp/gcm-header-priority-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Example
#eval observe [3, 2, 1]
-- some ([(3, 0), (3, 0)], ["muli", "ult", "addi", "muli"], [none, none, some 9])
#eval observe [1]
-- some ([], ["addi", "muli", "muli", "ult"], [none, none, some 9])
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-header-priority-example.lean

make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Thms +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Regression +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Sequence.Regression'
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Header.Priority.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[sequence]: sea-of-nodes-gcm-header-sequence.md
[corridor]: sea-of-nodes-gcm-corridor-placement.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Priority/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Priority/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Priority/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Header/Priority/Regression.lean
