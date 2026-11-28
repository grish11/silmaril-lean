# Replaying a dependent hoist after the first preheader move

Click's Schedule Early (§2.2) visits definitions before placing their
consumers. Schedule Late (§2.3) uses the source of the matching incoming
edge for a Φ operand. Section 2.4 chooses a block between those bounds.
This example applies the definition and use constraints to one nominated
consumer at one cut of the existing typed single-latch loop. It uses the
actual CFG emitted by the first checked hoist. [Proceedings][paper] ·
[Archived PDF][pdf] · [Sea of Nodes source map][coverage]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.

`AfterReorder.Second.prepare?` takes the native loop, an existing first
plan, and the consumer's original header binding identity. It replays the
header requests, resolves the producer on that reordered header, and
runs the existing corridor hoist. It removes the producer from the
tracked order and resolves the consumer on the resulting header. The
consumer can capture the producer's saved header argument and immutable
inputs, including the case where all operands come from inputs. A latch
argument or any remaining local result causes refusal. The saved operand's
definition is at preheader cut one, and immutable inputs are at cut
zero. The existing exact CFG cut checker tests cut one against those
definitions and the newly scanned uses, including exact branch slots and
successor argument indices. [Definitions][defs]

- `prepare?_replay_first` identifies the intermediate CFG with
  `AfterReorder.replay?`. The existing routing, same-fuel CFG execution,
  native budget (`fuel = budget + 3`), and partial denotation theorems
  apply to this emitted first CFG. [First hoist theorem header][first]
- `prepare?_placement` connects the tracked identities, the actual
  intermediate binding and use scan, and cut legality.
- `prepare?_available` identifies the actual leading preheader let and
  proves that the consumer evaluated from its result and the immutable
  inputs yields the current header binding's value for every latch value.
  `findCandidate?_value` is the corresponding typed capture law.
  [Theorem header][thms]

## Sequential emission

`AfterReorder.Second.Emit.replay?` applies the handoff to the one-save
CFG itself. It inserts the captured consumer at preheader cut one, after
the producer let, and removes the current header binding using a typed
substitution for its uses. The prefix retains its existing order. The
two-save header uses the existing slice layout `[consumer, producer, latch]`.
Entry and each feedback edge prepend the consumer result to the existing
packet. A remapped exit edge keeps its exact original argument values,
and the exit block keeps its return operands. [Emitter][emitter] ·
[Existing slice layout][slice]

`replay?_spec` identifies the exact first replay and second edit.
`prepare?_emits` proves every accepted handoff has the necessary typed
shape. `replay?_routes` proves the concrete entry insertion and header
rewrite with exact transfer equations against the first emission.
`replay?_run_eq` gives the same return or exhaustion at each CFG fuel.
`replay?_budget` transports the native law with `fuel = budget + 3`,
and `replay?_denotePart` gives partial denotation equality with the
native lowering. The proof uses the first hoist's invariant that the
producer result remains in its saved slot, the typed capture law, and
the existing two-save runner simulation. The profile is two nominated
pure total bindings in the existing single-latch loop. [Theorem header][emit-thms]

The example moves the comparison to the front and hoists producer
identity 1. Consumer identity 2 was at position 3 after reordering
and is now at position 2. Its operand cuts are `[1, 0]`, its ordinary
read is at header cut 3, and its false-edge argument 0 is read at cut 4.
The first CFG carries saved value 2 with latch values 3, 7 and 11,
then exits with value 3. The regression also checks a stale position,
reversed nominations, repeating the removed identity, and a consumer
that reads a latch-derived local result. [Example][example] · [Regression][regression]

The second edit changes the preheader/header binding counts from
`(3, 4)` to `(4, 3)`. The emitted entry and two feedback packets are
`[3, 2, 3]`, `[3, 2, 7]`, and `[3, 2, 11]`. The exit payload is `[3]`.
Native lowering uses the true occurrence for feedback and the false
occurrence for exit. A separate typed terminator regression routes the
false occurrence to the header and checks both argument tuples through
the same emitter helper. [Emitted example][emit-example] · [Emission regression][emit-regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Thms \
  +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Regression
cat >/tmp/gcm-second-hoist-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Example
#eval observe false -- some (2, (4, 3), [[3, 2, 3], [3, 2, 7], [3, 2, 11], [3]])
#eval observe true -- none
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-second-hoist-example.lean
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Emit.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Regression.lean
[first]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Thms.lean
[slice]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Defs.lean
[emitter]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Emit/Defs.lean
[emit-thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Emit/Thms.lean
[emit-example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Emit/Example/Defs.lean
[emit-regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Emit/Regression.lean
