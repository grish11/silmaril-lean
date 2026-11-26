# Discovering checked single-latch hoists

Click's Schedule Early orders a definition before its consumers (§2.2).
Schedule Late accounts for Φ reads on the matching incoming CFG occurrence
(§2.3). A final position can affect another instruction's legal placements
(§2.4). This slice discovers nominations on the current typed CFG by
rechecking the remaining header after each successful edit.
[PLDI ’95 proceedings][paper] · [Archived PDF][pdf] · [Source map][coverage]

The archived PDF has SHA-256
`9b2fae161f346d545a85af481ce7f8b1e5921e77a4fa17ee373780249206aa23`.

`Replay.Discovery.discover` starts with a native pure, total single-latch
loop and optional checked header reorder requests. It visits the remaining
original identities in current header order and takes the first nomination
whose actual checker and emitter succeed. The first move nominates preheader
cut 0, where the existing synthesized corridor must also select that cut.
The second nominates cut 1. Each subsequent move nominates the end of the
contiguous leading saved prefix on the current CFG. The existing checkers
resolve the typed binding, capture available operands, and account for the
current ordinary reads and exact Φ occurrences. The successful emitters
retain the checked routing for the saved values, latch and exit.
[Definitions][defs] · [Replay and splice][replay]

The continuation starts with a budget equal to the number of unsaved header
identities. `collect_count` shows that every successful move removes one.
`collect_origins` ties that inventory to the emitted header operations.
`collect_exhausted` proves the sufficient budget leaves no eligible
continuation. `next?_none_iff` characterizes exhaustion for each replay
phase against all nominations that its checker could accept, including the
cut and identity tests.

`discover_spec` proves the full plan replays to the exact returned typed CFG,
the surviving identities match its header, and every nomination fails on the
terminal CFG in its current replay phase. `discover_run_eq`,
`discover_budget`, and `discover_denotePart` reuse the replay laws for common
fuel, native backedge budgets, and partial denotation.
[Theorem header][thms]

The search is greedy and local to the supported replay profile. The initial
corridor's existing block choice still applies. Later moves can read only
immutable inputs, saved slots, or a mix. Exhaustion refers to the terminal CFG
reached by the choices actually made. Other starting choices, placements in
other blocks, and global scheduling quality are outside the claim.

For an immutable-only capture, `findCaptured?_immutable` identifies every
operand's definition at entry cut 0 and proves that its typed value agrees
with the original input under any saved prefix. `Step.emit_immutable` proves
legality at the actual append cut and equality with the binding's value on
the current header for every latch argument. A latch argument or another
unhoisted header result is a local origin and fails operand capture.
The new scanner returns the same
candidate and use sites for earlier saved-dependent successes, and
`prepareOn?_of_saved_capture` and `emit_of_saved_capture` retain their exact
handoff and emission. [Capture theorems][captures] · [Checked step][step]

## Operand availability within the saved prefix

Click's Schedule Early (§2.2) finds the earliest block dominated by all
inputs. Within the fixed preheader, `Candidate.earliestCut` refines that input
constraint to local binding order. It takes the maximum defining cut of the
captured typed references, with cut zero for immutable inputs. A read of
saved slot `i` (newest first) requires at least cut `prefixLength - i`, even
if every other operand is immutable. `findCaptured?_sites` ties the recorded
definitions to the typed capture. Given a successful split of the current
entry at the saved prefix, `findCaptured?_operandCut_iff` proves that the
closed interval from `earliestCut` through the prefix end contains exactly
the valid prefix cuts where all operands are available.

`checkPrefixCut` also checks the ordinary uses and the actual incoming Φ
occurrences (§2.3). The second and later discovery phases use it at the
prefix end on each current CFG. `findCaptured?_checkConsumer_eq` proves the
added interval check yields the same append decision for every typed capture.
Schedule Late's block selection and loop-depth ranking (§§2.3–2.4) are outside
this local interval. Discovery still nominates the prefix end. Explicit
nominations can use the earlier insertion below.
[Capture theorems][captures] · [PLDI ’95 proceedings][paper]

The runnable chain discovers origin/cut pairs `(1, 0)`, `(2, 1)`, and
`(5, 2)`. The third binding needs both earlier results. Two variants keep
the same plan with an immutable-only binding at cut 1 or cut 2. A variant
with a latch-dependent operand stops after `(1, 0)`, and a loop whose
candidates all depend on the latch stops before the first move. On the actual
one-save CFG the immutable consumer has interval `[0, 1]`. On the actual
two-save CFG a consumer of the older save has interval `[1, 2]`, passes the
use check at both cuts, and still replays at cut 2. Latch and header-local
reads both fail capture.
[Example][example] · [Regression][regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Thms \
  +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Regression
cat >/tmp/gcm-hoist-discovery-example.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Example
#eval observe chain
#eval observe immutableSecond
#eval observe immutableLater
#eval observe varying
#eval observe unsaved
#eval immutableInterval
#eval savedInterval
#eval rejectedIntervals
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-hoist-discovery-example.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.AfterReorder.Second.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Discovery.Thms
```

## Emitting an earlier saved-prefix cut

`Replay.Step.Earlier.emit?` inserts one checked pure, total header binding
at a nominated cut strictly before the end of the current saved prefix. It
resolves the original identity through the existing append step and runs
`checkPrefixCut` for the nominated cut on the same input CFG. This combines
Click's input-availability condition (§2.2) with the ordinary and exact
incoming Φ use checks (§2.3). The original append step supplies the rewritten
header, including both branch arms and the exact exit. [Emitter][earlier-defs]
· [PLDI ’95 proceedings][paper]

`Saved.Prefix.insert?` splits the physical insertion position by the count
of later saves. It narrows the candidate's typed operands at each crossing,+refusing a read of the crossed value. It rebuilds the later saves in order
and remaps their operands. `insert?_indices` relates the physical index to
the cut and gives the index of each old reference. `insert?_eval` proves
that reading the physical scope through `Insertion.toPhysical` returns the
new value followed by the old logical scope. The entry tail uses that map
to build the same packet as append, while the shared header uses its original
logical packet order. `emit?_entry_targets` compares actual entry successor
slots, `Emission.block_eq` preserves the labeled blocks, and `emit?_routes`
gives the entry, feedback, and exit transfer law. [Prefix proofs][insert-thms]
· [Emitter proofs][earlier-thms]

`emit?_run_eq` and `emit?_denotePart` compare the actual earlier and append
CFGs at every common block fuel and for partial denotation. The let order
changes within one block, so fuel consumes the same blocks. Starting at the
checked two-save replay of a native loop, `emit?_fromTwo_budget` compares CFG
fuel `budget + 3` with native backedge budget `budget`.

The example inserts at cut 1 between two prior saves. In chronological order,
the three saved words are `2, 4, 3`, and the newest-first logical packet is
`4, 3, 2` before the carried word. The later save needs the first save, so
its input must be remapped across the insertion. Two feedback packets keep
that order and the `.onFalse` occurrence carries the exact exit word. An
immutable-only variant crosses both saves at cut 0. The fixture refuses cuts
before the older or newer saved producer, a latch read, and a stale origin.
[Example][earlier-example] · [Regression][earlier-regression]

Append replay and discovery still use their established physical slot order.
The explicit earlier result also supports one checked follow-on placement
through the interface below. Cut selection stays with the caller and
Click's loop-depth ranking (§2.4) stays in the existing placement APIs.

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Thms \
  +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Regression
cat >/tmp/gcm-earlier-prefix.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Example
#eval observe
#eval beforeBoth
#eval refused
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-earlier-prefix.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Saved.Prefix.Insert.Thms
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Thms
```

## Placing a dependent binding after an earlier splice

`Replay.Step.Earlier.Follow.emit?` takes the earlier emission and a nomination
in its current preheader coordinates. It resolves the original identity in
the surviving header, which the earlier CFG shares with its append reference.
The capture names logical saved slots and immutable inputs. `physicalOperands`
renames that tuple with the earlier insertion's typed map. Each renamed
reference determines its defining cut in the physical prefix. The existing
cut checker runs on the actual earlier CFG with these cuts and the unchanged
ordinary and exact incoming Φ occurrences. The same typed splice inserts
the new let, remaps the crossed saves, and lifts the actual entry tail.
[Definitions][follow-defs] · [Click §§2.2–2.4][paper]

`physicalOperands_eval` relates every remapped read to the actual append
prefix's logical value. `savedCount_eq` proves that both scopes have the same
number of saves. `emit?_placement` identifies the current header binding and
certifies the physical cut. `emit?_routes` proves both actual transitions add
their values to the logical entry and feedback packets and preserve the exact
exit transfer. `emit?_entry_targets` preserves successor slots and the labeled
blocks are shared with the two-append result. `emit?_append_replay` identifies
that exact reference CFG. The run and partial-denotation laws compare the two
emitted CFGs at common block fuel. With the verified native seed, block fuel
`budget + 3` again corresponds to native backedge budget `budget`.
[Theorems][follow-thms]

The fixture first puts origin 5 at cut 1. Origin 6 reads origin 5, whose
definition is at cut 2 in that physical prefix and cut 3 in append order.
Origin 6 therefore inserts at physical cut 2, ahead of the last old save.
For inputs `2, 10, 1`, the physical definitions evaluate in the order
`2, 4, 5, 3` and the logical packet starts with `5, 4, 3, 2`. Two feedbacks
carry those words in that order and the `.onFalse` exit argument is `5`.
A cut before the remapped producer, a stale origin, and a latch read are
refused. The one-follow-on API uses the same transition as the finite replay
below. [Example][follow-example] · [Regression][follow-regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Thms \
  +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Regression
cat >/tmp/gcm-layout-followup.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Example
#eval observe
#eval refused
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-layout-followup.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Earlier.Follow.Thms
```

## Replaying a finite list of physical placements

`Replay.Step.Layout.initial?` splits the actual canonical saved prefix and
starts with identity slot correspondence. `Follow.toLayout` also exposes the
layout of a successful earlier emission. `Layout.State` keeps the typed
physical prefix and entry tail, the logical append reference, and a typed
map from logical slots to physical definitions. `Layout.emit?` checks the
current header capture and physical cut using the existing ordinary and
incoming Φ uses. The splice maps the new slot to the insertion and composes
the previous map with its remapping of kept definitions. `emit?_physicalSlot`
gives the exact update for original saved identities. [Definitions][layout-defs]
· [Click §§2.2–2.4][paper]

`emit?_placement` certifies the current captured binding and cut on the
actual CFG. `physicalOperands_eval` identifies the values read through the
map. `emit?_invariant` preserves that correspondence, the entry's successor
slots and exact evaluated entry packet. The actual labeled blocks are shared
with append, so the header's branch slots and incoming Φ operands retain
their reference order. `run_spec` identifies the exact append result for
any accepted finite plan and certifies the output layout. `emit?_routes`
and `run_packets` preserve the logical packets at one step and across the
list, using the existing certified reference packet invariant.
[Theorems][layout-thms]

`Layout.run` takes caller-nominated original identities and cuts in each
current physical prefix. Refusal reports the first invalid nomination and
returns no CFG. Successful execution agrees with checked append at the same
CFG block fuel and in partial denotation. From the checked two-save native
seed, `run_fromTwo_budget` relates fuel `b + 3` to backedge budget `b`. The
supported profile is a pure, total single-latch loop with an existing saved
prefix. The finite driver leaves cut selection and discovery to the caller.

The fixture replays `(5, 1)`, `(6, 2)`, and `(7, 3)`. Origin 7 reads the
results of both earlier moves at physical cuts `3, 2`, with logical append
cuts `4, 3`. For inputs `2, 10, 1`, the final physical definitions evaluate
in order `2, 4, 5, 9, 3`. Entry and both feedbacks carry the saved words
`9, 5, 4, 3, 2` before the carried word, then the exact `.onFalse` exit
argument is `9`. Replacing the last request with either a cut before the
physical operand or a stale saved identity reports refusal at position 4.
[Example][layout-example] · [Regression][layout-regression]

```sh
lake build --wfail +Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms \
  +Silmaril.Proofs.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Regression
cat >/tmp/gcm-layout-replay.lean <<'LEAN'
import Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example.Defs
open Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Example
#eval observe
#eval refusal ⟨7, 2⟩
#eval refusal ⟨6, 3⟩
LEAN
lake env lean -DwarningAsError=true /tmp/gcm-layout-replay.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.GCM.LoopHoist.Corridor.Replay.Step.Layout.Thms
```

[paper]: https://doi.org/10.1145/207110.207154
[pdf]: https://web.archive.org/web/20140908214434id_/https://courses.cs.washington.edu/courses/cse501/06wi/reading/click-pldi95.pdf
[coverage]: ../coverage.md#global-code-motionglobal-value-numbering
[replay]: sea-of-nodes-gcm-replay.md
[defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Discovery/Defs.lean
[thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Discovery/Thms.lean
[example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Discovery/Example/Defs.lean
[regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Discovery/Regression.lean
[captures]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/AfterReorder/Second/Thms.lean
[step]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Thms.lean
[earlier-defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Earlier/Defs.lean
[earlier-thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Earlier/Thms.lean
[earlier-example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Earlier/Example/Defs.lean
[earlier-regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Earlier/Regression.lean
[insert-thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Saved/Prefix/Insert/Thms.lean
[follow-defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Earlier/Follow/Defs.lean
[follow-thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Earlier/Follow/Thms.lean
[follow-example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Earlier/Follow/Example/Defs.lean
[follow-regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Earlier/Follow/Regression.lean
[layout-defs]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/Defs.lean
[layout-thms]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/Thms.lean
[layout-example]: ../../../../Silmaril/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/Example/Defs.lean
[layout-regression]: ../../../../Silmaril/Proofs/SSA/SeaOfNodes/GCM/LoopHoist/Corridor/Replay/Step/Layout/Regression.lean
