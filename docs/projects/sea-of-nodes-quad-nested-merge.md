# A nested quad split with three incoming merge occurrences

Cliff Click's *From Quads to Graphs* §3.1 describes inspecting the
current definitions on every parsed path in nested if/then/else
structures before inserting Φ instructions at the merge. Figure 6
shows how each write updates the current-definition map. The source
is Rice TR CRPC-TR93366-S (October 18, 1993), SHA-256
`8b13190b36a8aae0b7b1e622337d99263662487e18144d8e1b379dcea580548b`.
[Archived manuscript](https://web.archive.org/web/20250330055404id_/https://softlib.rice.edu/pub/CRPC-TRs/reports/CRPC-TR93366-S.pdf)

`Quads.Loop.Tail.Nested.check` reads the original quad table. The outer
true edge enters a second split. The inner true, inner false and outer
false occurrences run along disjoint jump segments to one common merge,
in that column order. A direct edge contributes the split itself as
predecessor, with the definitions after its ordered quads. Both inner
arms may enter the merge directly and contribute separate occurrences
from the same block. The merge
jumps to a distinct tested latch whose true edge feeds back to the
header and whose false edge returns. The discovered blocks must cover
the table exactly once. An inner edge that skips the common merge and
goes straight to the latch is refused.
[Checker](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Defs.lean)

`Program.incomingTransfer` compiles the ordered quads of each path into
its own typed reaching-version map. `Program.merge_bank` validates each
map's complete bank. `Program.run_to_merge` identifies the column read
by the source runner and charges each visited split and each block of
the selected segment, stopping before the merge body.
[Source theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Thms.lean)

`Nested.MLIR.CF.prune` uses the existing carried mask and checks that
the smaller header can reconstruct the full post-header bank.
`Nested.MLIR.CF.lower` reuses the typed CF emitter with both original
split IDs and all source terminators. Each merge edge supplies the
register bank from its own final versions. Only edges into the header
use the smaller bank. `from_header_eq_merge` relates execution of the
emitted path to resuming at the merge with the source-computed column.
`lower_run` preserves the return or exhaustion at source budget `n`
and CF budget `n + 1`. The extra visit executes the typed return label.
This profile carries the full bank at the common merge and has one
nested split and one checked backedge.
[CF theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MLIR/CF/Thms.lean)

Build the fixture with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example.Defs`.
Paste the following into `QuadNestedMerge.lean` and run
`lake env lean -DwarningAsError=true QuadNestedMerge.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MLIR.CF.Example

#eval predecessors                 -- [3, 2, 4]
#eval incomingResults              -- [7, 6, 10]
#eval (runSource 14, runCF 15)      -- (some 16, some 16)
#eval (runSource 13, runCF 14)      -- (none, none)
```

The first two lines read the three columns from the same initial
header bank. Execution takes two feedback edges and visits the merge
from blocks 3, 2 and 4 with results 7, 8 and 16. The regression checks
the three emitted merge packets, both projected feedback frames, and
the refusal case. The overwritten predicate reduces the carried bank
from seven fields to six.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MLIR/CF/Regression.lean)

## Run the numbered γ/θ graph

`Nested.Numbered.lower` emits a carried θ with the same header
reconstruction certificate as CF. The outer γ's true region executes
the inner split's quads and contains a second numbered γ. A direct
inner edge forwards the post-inner bank. The outer false region
executes its own arm quads. Neither split duplicates the common merge
or the tested latch. `checkResult` certifies that the θ stopping packet
retains the source return slot.
[Numbered emitter](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Numbered/Defs.lean)

`merge_run` connects the actual numbered routes to the corresponding
`Program.incomingTransfer` column. The graph resolves names in each
region's typed scope and supplies the same bank as the source column's
whole-path scope. `activation_run` gives the original stop/restart tag
and the simultaneous projected feedback bank. `returns_iff` connects
finite source returns with finite θ returns in both directions.
[Numbered theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Numbered/Thms.lean)

`Comparison.cf_returns_iff` compares the same typed input and
the same encoded result with a separate budget witness for each
target. `cf_at_activations` counts the visited source blocks on the
selected paths, plus one CF return visit. `cf_diverges_iff` compares
absence of a return at every finite budget.
[Comparison theorems](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Numbered/Comparison/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Example.Defs`.
Paste the block into `QuadNestedNumbered.lean` and run
`lake env lean -DwarningAsError=true QuadNestedNumbered.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Numbered.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested

#eval Numbered.Example.incoming
#eval Numbered.Example.thetaArity
#eval (Numbered.Example.sourceBudget 3, MLIR.CF.Example.runCF 15, Numbered.Example.runRVSDG 3)
#eval (MLIR.CF.Example.runCF 14, Numbered.Example.runRVSDG 2)
```

The three γ probes return `[(3, some 7), (2, some 6), (4, some 10)]`.
The numbered θ carries six fields, down from the seven source registers.
Three activations take two feedback edges and return 16 at CF budget 15.
The last line shows bounded exhaustion in both targets.
[Numbered regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Numbered/Regression.lean)

## Project the common merge bank

The join projection is separate from θ's carried-header projection.
Section 3.1 gathers changed definitions on all reaching paths. This
pass projects those columns when the merge replaces an incoming field
before any read. `MergePrune.mergeMask` uses the existing backward
producer sweep. `checkMask` validates typed renaming for every merge
producer and requires reconstruction of the **complete**
post-merge bank before entering the latch. This admits overwritten
inputs and keeps any unchanged slot that reaches the latch, even if
the merge itself never reads that slot. It is a conservative check
for this one merge.
[Projection certificate and reconstruction](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Thms.lean)

The numbered emitter removes the field from the outer γ's result
signature and from both of its output packets, preserving the original
nested γ and selection order. It uses in-scope header wires to fill
dropped inputs for the ordinary quad compiler. The certificate proves
those choices have no effect on the full reconstructed post-merge bank.
The typed CF emitter gives the original merge label the smaller block
signature. Every predecessor sends the same ordered projection of its
own final versions. The merge emits the certificate's renamed flow and
full outgoing bank. The original θ header projection is still applied
separately.
[Numbered proofs](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Numbered/Thms.lean) ·
[Typed CF proofs](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/MLIR/CF/Thms.lean)

`Numbered.merge_run` and `MLIR.CF.from_header_eq_merge` identify the
smaller bank at the selected source occurrence. Both targets preserve
their corresponding full-merge runner at every budget. The comparison
theorems transfer finite return witnesses across targets and compare
absence of a return at every finite budget.
[Comparison](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Comparison/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Example.Defs`.
Paste the block into `QuadNestedMergePrune.lean` and run
`lake env lean -DwarningAsError=true QuadNestedMergePrune.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Example

#eval columns                          -- [(3, 41, some 7), (2, 42, some 6), (4, 43, some 10)]
#eval arities                          -- (6, some 6)
#eval refusesUsed                      -- (true, true)
#eval (runSource 14, runCF 15, runRVSDG 3)
#eval (runSource 13, runCF 14, runRVSDG 2)
```

Each row names the original predecessor, its distinct dead scratch
input, and the returned field from the actual reduced γ. Both emitted
join interfaces carry six of seven fields. The checker refuses to
drop the value read by the merge or the counter that crosses the
merge to the latch. Two feedback edges lead to a return of 16 in
all three runners, and the last line gives three exhausted runs.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Regression.lean)

## Drop inputs that survive the merge

Section 3.1 tracks the current definition at each incoming occurrence.
The merge–latch check starts with those definitions and follows the
ordered quads through the tested latch. `Latch.mergeMask` runs the
existing backward sweep over every producer. The final reads are the
resolved latch condition, return word and the actual θ-carried feedback
wires. `Latch.checkMask` validates those typed wires and all producer
operands. The pure profile retains every ordered producer.

`Latch.Checked.incoming_agrees` recovers that entire packet from the
smaller bank of any of the three occurrences. The complete post-merge
bank can differ. `Latch.Numbered.lower` emits the smaller outer γ and
reuses the original θ and arm routing. The checked packet proves that
the in-scope fillers for dropped wires have no effect on the branch,
return or retained feedback. The comparison reuses the existing
source and CF budgets, including absence of any finite return.
This comparison uses the full-merge CF emitter. The next section
gives the narrower CF emitter and its checked merge-to-latch edge.
[Certificate](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Thms.lean) ·
[Numbered emitter](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Numbered/Thms.lean) ·
[CF comparison](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Comparison/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Example.Defs`.
Paste into `QuadMergeLatch.lean` and run
`lake env lean -DwarningAsError=true QuadMergeLatch.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Example

#eval columns
#eval gammaArity
#eval overwriteAdmission
#eval refusesUsed
#eval tailPackets
#eval (runSource 14, runCF 15, runRVSDG 3)
#eval (runSource 13, runCF 14, runRVSDG 2)
```

The routes from blocks `[3, 2, 4]` bring decrement values
`[41, 42, 43]` and retained words `[7, 6, 10]` on the three
probe inputs. The common merge leaves the decrement unchanged.
The latch writes `255` before using or feeding it back. The emitted
γ carries five of seven fields. `overwriteAdmission` reports that
dropping only the decrement passes the packet check and fails the
complete-bank check. `refusesUsed` checks the merge operand, a latch
guard supplied by an incoming definition, a carried field used only
after feedback, and the original live latch counter. The successive
latch packets show two continuing activations and a stop returning
`16`. All three runners return `16` at budgets `14/15/3` and
exhaust at the smaller bounds.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Regression.lean)

## Emit the checked merge-to-latch interface in CF

`Latch.Split.prepare` starts with the shared merge–latch certificate.
The backward sweep on the separate latch keeps every producer operand,
the resolved guard and return word, and every field of the projected
header feedback. The checker then validates two typed transfers. The
merge sends just the needed latch inputs in register order. The latch
computes the same packet as the shared certificate. `Split.check` can
also validate a supplied latch mask.
[Checked interface](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Split/Thms.lean)

`Latch.MLIR.CF.lower` reuses the existing projected header and merge
labels and sends the original latch edges to its narrower block
signature. The wrapped label family retains a full-width latch label,
but all edges to the latch use the projected label. The additional cut
check can refuse a mask if either locally scoped transfer cannot be
renamed. `selected_predecessor_frame` identifies the actual emitted
incoming frame from each selected original predecessor. This includes
the inner split's direct edge and its post-inner definitions.
`merge_frame` gives the actual merge-to-latch arguments, and
`latch_frame` gives the selected exit word or simultaneous feedback
frame. The merge and latch still execute as separate source visits.
`lower_run` preserves the source budget `n` at CF budget `n + 1`,
including exhaustion. Only the final typed CF return adds a visit.
The comparison with the narrower numbered graph transfers finite
return witnesses at independent budgets and proves agreement when
neither runner returns at any finite budget.
[CF proofs](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/MLIR/CF/Thms.lean) ·
[Numbered comparison](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/MLIR/CF/Comparison/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Example.Defs`.
Paste into `QuadMergeLatchCF.lean` and run
`lake env lean -DwarningAsError=true QuadMergeLatchCF.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch

#eval Example.columns
#eval MLIR.CF.Example.incomingArities
#eval MLIR.CF.Example.latchArity
#eval Example.refusesUsed
#eval (Example.runSource 14, MLIR.CF.Example.runCF 15, Example.runRVSDG 3)
#eval (Example.runSource 13, MLIR.CF.Example.runCF 14, Example.runRVSDG 2)
```

All three emitted merge edges and the subsequent latch edge carry five
of seven fields. The latch resets the dropped decrement to `255`.
The regression checks the exact emitted merge and latch packets on
both backedges and the exit, which returns `16`. It also checks the
merge operand, incoming latch guard, feedback field and counter refusals.
The interface covers the checked pure nested split, common merge and
tested latch.
[CF regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/MLIR/CF/Regression.lean)

## Remove an unused pure latch producer

Section 3.1 tracks which definition each use reads. Section 3.2 uses
those references to analyze the instructions. On the checked latch table, `Split.DeadProducer.first` reuses the existing GVN
producer enumeration and typed eraser to try one deletion in table
order. The eraser refuses an unmapped operand of any surviving
instruction. The check also requires every outgoing wire to remap,
including the resolved guard, exit word and simultaneous feedback.
This retains all transitive dependencies of those observations.
The packet theorem holds for every input to the narrowed latch.
[Typed eraser](../../Silmaril/SSA/SeaOfNodes/GVN/Cyclic/Deletion/Thms.lean) ·
[Checked packet](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Split/DeadProducer/Thms.lean)

`Latch.MLIR.CF.DeadProducer.lower` emits the shorter table in the
original latch block with the same typed terminator and labels.
`latch_packet` and `latch_frame` relate the actual emitted branch to
the checked packet. `lower_run` keeps the original source/CF budget
relation `n` to `n + 1`. Finite returns and absence of any finite return
agree with the source and with the existing numbered RVSDG endpoint,
which uses its own θ activation bound. The pass removes one pure
total binding from the CF latch on each accepted cut.
[CF proofs](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/MLIR/CF/DeadProducer/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Example.Defs`.
Paste into `QuadLatchDeadProducer.lean` and run
`lake env lean -DwarningAsError=true QuadLatchDeadProducer.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.MLIR.CF.DeadProducer.Example

#eval latchCounts
#eval refuses
#eval (runSource 14, runCF 15, runRVSDG 3)
#eval (runSource 13, runCF 14, runRVSDG 2)
```

The initial comparison writes a predicate that the final comparison
replaces before any use. Its deletion reduces the actual latch from
five operations to four. The checker refuses to delete the constant
`254` that feeds the decrement computation, the live counter update,
or the final guard. The regression checks incoming edges in the
original order `[3, 2, 4]` and both exact feedback frames. The three
runners return `16` at budgets `14/15/3` and exhaust one unit below.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/MLIR/CF/DeadProducer/Regression.lean)

## Emit the same shortened latch in numbered RVSDG

`Latch.Numbered.DeadProducer.lower` takes the same checked deletion as
the CF emitter. The original γ arms deliver the selected merge column
in §3.1 order. `GVN.Elimination.plug` substitutes that column for the
merge arguments, then substitutes the narrowed merge outputs for the
shortened latch arguments. `plug_read` proves that both substitutions
preserve reads in the enclosing numbered scope.
[`plug_read`](../../Silmaril/SSA/SeaOfNodes/GVN/Elimination/Thms.lean)

`packet_run` gives the exact source guard, exit word and feedback tuple.
`activation_run` gives the actual θ tag and simultaneous carried bank.
The stopping bank supplies the retained return slot. `returns_iff` and
`noFiniteReturn_iff` compare with the source at finite bounds, while
`Comparison.cf_at_activations` also accounts for the extra CF return
visit. The comparison includes both finite-return witnesses and absence
of any finite return. A `none` at one concrete bound means exhaustion.
[Numbered proofs](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Numbered/DeadProducer/Thms.lean) ·
[CF comparison](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Numbered/DeadProducer/Comparison/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Example.Defs`.
Paste into `QuadNumberedLatchDeletion.lean` and run
`lake env lean -DwarningAsError=true QuadNumberedLatchDeletion.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.Numbered.DeadProducer.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch
open Numbered.DeadProducer.Example
open MLIR.CF.DeadProducer.Example (refuses runSource runCF)

#eval latchTests
#eval predecessorOrder
#eval feedback
#eval refuses
#eval (runSource 14, runCF 15, runNumbered 3)
#eval (runSource 13, runCF 14, runNumbered 2)
```

The emitted θ latch changes from `[true, false, false, false, true]`
to `[false, false, false, true]`, where `true` marks a comparison. The
run takes predecessors `[3, 2, 4]` and emits `(tag, counter, word)`
packets `(1, 2, 7)`, `(1, 1, 8)` and `(0, 0, 16)`. All three live cuts
above still fail. The three runners return `16` at `14/15/3` and exhaust
one unit below. This covers one checked pure latch deletion in the
nested split, common merge and tested latch profile.
[Numbered regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/Numbered/DeadProducer/Regression.lean)

## Rescan the shortened latch

`Latch.DeadProducer.Iteration.prepare` starts with the checked latch's
ordered table and its entire guard, exit and simultaneous feedback
packet. Section 3.2 uses explicit use-def edges to analyze related
instructions. Removing an unused consumer can make its producer
unused. The iterator scans the current typed table
from the beginning after each checked deletion. Each accepted step
removes one binding. The initial size bounds the number of cuts, and
one final scan certifies that the checker accepts no current producer.
The recorded positions use the numbering before each cut.
[Deletion laws](../../Silmaril/SSA/SeaOfNodes/Pure/Deletion/Iteration/Thms.lean)

`lowerCF` and `lowerNumbered` consume the same `Prepared` value. Its
proof preserves the complete packet for every input. The CF emitter
uses the original latch label. The numbered emitter uses the original
γ routing and substitutes the merge's actual outputs into the final
table. The proofs compare finite returns and absence of any finite
return. CF uses the source visit count plus one return visit, and θ
uses an activation count. This pass shrinks the producer table within
the checked pure latch interface.
[Emitter laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/DeadProducer/Iteration/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Example.Defs`.
Paste into `QuadLatchIteration.lean` and run
`lake env lean -DwarningAsError=true QuadLatchIteration.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Example

#eval (refusesBeforeRescan, prepared.positions, settled)
#eval latchCounts
#eval feedbackCheck
#eval (predecessorOrder, feedback)
#eval (runSource 14, runCF 15, runNumbered 3)
#eval (runSource 13, runCF 14, runNumbered 2)
```

The first comparison is deleted at position `1`, making its constant
deletable at position `0` on the next scan. Both actual emitted latches
shrink from seven operations to five. The guard and exit alone would
allow deleting the last stride update. The full packet refuses the cut
because its only use is at zero-based feedback slot `3`. The fixture
takes predecessors `[3, 2, 4]` and returns `16` after two feedback steps,
at source, CF and θ budgets `14/15/3`. Each runner exhausts one unit below.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/DeadProducer/Iteration/Regression.lean)

## Compile the original quad table

`Backends.compile` takes the ordered source table and entry ID. It uses
the original §3.1 recognizer, reports `.shape` when that check refuses,
and otherwise passes through the first failed projection, split or
result-port check. `compileChecked` accepts an existing checked
`Program`. On success the compiler prepares the latch once and stores
both typed artifacts as `targets.cf` and `targets.numbered`.
[Compiler](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/DeadProducer/Iteration/Backends/Defs.lean)

`Targets.numbered_packet` and `Targets.cf_activation_packet` identify
the exact packet or selected frame after the original selected path.
`Targets.cf_run` uses source visits plus the CF return visit, and
`Targets.numbered_run` uses θ activations. `Targets.returns_iff`
quantifies source, CF and θ budgets independently for each value.
`Targets.noFiniteReturn_iff` characterizes exhaustion at every bound.
The compiler uses the checked pure nested shape and the existing
strict header and merge projections.
[Compiler laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/DeadProducer/Iteration/Backends/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Example.Defs`.
Paste into `QuadNestedCompile.lean` and run
`lake env lean -DwarningAsError=true QuadNestedCompile.lean`.

```lean
module

meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends

#eval (compile Example.source 0).map Example.report
```

The accepted run records cuts `[1, 0]`, five latch operations in each
emitted target, and the protected stride use at feedback slot `3`.
It traverses predecessors `[3, 2, 4]` and returns `16` at source, CF,
and θ budgets `14/15/3`. The same compiled pair exhausts one unit
below. The regression checks `.shape` for the edge that skips the merge
and `.headerProjection` for a recognized full-bank header.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/DeadProducer/Iteration/Backends/Regression.lean)

### Parallel inner edges into the common merge

The two empty inner arms exercise §3.1's rule to inspect every path to
the merge. They carry the same latest definitions because both leave
the inner split immediately after its writes. `Program.incomingEdge`
identifies each incoming occurrence by its original predecessor and
outgoing slot. `Program.parallel_inner_merge` proves that the post-inner
predicate selects slot 0 or 1, that the selected compiled column gives
the full post-inner bank, and that reaching the merge costs two source
visits. The disjoint-block check still refuses two arms sharing a
nonempty segment, and exact table coverage remains mandatory.
[Occurrence law](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Thms.lean)

Build the same `Backends.Example.Defs` module as above. Paste into
`QuadNestedParallel.lean` and run
`lake env lean -DautoImplicit=false -DwarningAsError=true QuadNestedParallel.lean`.

```lean
module

meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends

#eval (compile Example.parallelInner 0).map fun targets =>
  (Example.parallelTrace targets, Example.runAt targets 13 14 3, Example.runAt targets 12 13 2)
#eval (compile Example.sharedInnerArm 0).map fun _ => ()
```

The three activations select `(2, 0)`, `(2, 1)`, and `(3, 0)`, with
guard and exit packets `(true, 6)`, `(true, 7)`, and `(false, 14)`.
The emitted CF keeps both slots of the original conditional. The source,
CF and numbered θ return `14` at budgets `13/14/3` and exhaust one unit
below. The existing completion theorem gives a finite coloured completion
for the same numbered graph. The shared nonempty arm is refused as
`.shape`. The extension covers parallel edges that go directly into the
existing common merge. A separate check below admits an inner-only
shared segment before the merge.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/DeadProducer/Iteration/Backends/Regression.lean)

### Shared inner jump suffix

Section 3.1 inspects the latest definitions on each incoming path at a
nested merge. `Nested.Shared.check` finds the first common inner block
before the original merge. It keeps the two checked prefixes, one
nonempty shared jump segment, and the outer false route. The block order
accounts for every original ID exactly once. Overlap with the outer
route fails the check.
[Checker](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Defs.lean)

`Program.innerEdgeOccurrence` records the predecessor and outgoing slot
for each of the two inner inputs. `run_prefix` reads the selected
prefix's full reaching bank. `run_suffix` executes the shared blocks once
on that bank, ending at the original merge. `run_to_merge` gives the
composed packet and exact visit count, including the outer false route
which enters the original merge directly from its own segment.
[Source laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Thms.lean)

`Shared.MLIR.CF.lower` reuses the full-bank typed CF emitter, with each
shared block at its original label. `from_header_eq_prefix` and
`from_header_eq_merge` give the exact compiled banks at both
boundaries. `lower_run` compares the source at budget `n` with CF at
`n + 1`. `returns_iff` and `noFiniteReturn_iff` compare finite returns
and absence of any finite return.
[CF laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/MLIR/CF/Thms.lean)

Build with
`lake build --wfail +Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Example.Defs`.
Paste into `QuadNestedShared.lean` and run
`lake env lean -DautoImplicit=false -DwarningAsError=true QuadNestedShared.lean`.

```lean
module

meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.Example

#eval plan.suffix.blocks.map Fin.val
#eval columns
#eval trace
#eval (runSource 19, runCF 20, runSource 18, runCF 19)
#eval (check outerOverlap 0).isNone
```

Both inner inputs reach blocks `[5, 6]`, which double the result and add
one. With the same starting bank, the two columns give `[(7, 15), (12, 25)]`
before and after the suffix. The actual loop takes inner true, inner
false and outer false, with merge values `15, 65, 130` and two feedback
edges. Source and CF return `130` at `19/20` and exhaust at `18/19`.
The near miss sends the outer route into block 6 and is refused.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/MLIR/CF/Regression.lean)

### Numbered θ and coloured completion for the shared suffix

`Shared.Numbered.lower` consumes the same checked source plan. The
inner γ children contain the two prefixes. The suffix uses the returned
wires of that γ and appears once inside the outer true region. The
outer false region passes its own bank to the outer γ and bypasses the
suffix. The θ body consumes the selected outer result and returns the
source latch tag and full post-latch bank on either feedback or exit.
[Emitter](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Numbered/Defs.lean)

`merge_run` gives the source-computed selected bank. `activation_run`
gives the actual numbered body's tag and simultaneous bank.
`lower_run` compares the θ activation budget with the sum of the
original source visits on its selected routes. `returns_iff` and
`noFiniteReturn_iff` quantify source and θ bounds independently.
`petri_finishes_iff` uses the existing coloured firing model on the
actual emitted graph. Its finite firing witness has its own length.
[Numbered laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Numbered/Thms.lean) ·
[Completion law](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Numbered/Petri/Thms.lean)

Build `Shared.Numbered.Example.Defs` and `Shared.Numbered.Petri.Thms`
with `lake build --wfail` and a `+` before each full module name below.
Paste into `QuadNestedSharedNumbered.lean` and run
`lake env lean -DautoImplicit=false -DwarningAsError=true QuadNestedSharedNumbered.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Numbered.Example
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example (input width)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (model)
open Silmaril.SSA.SeaOfNodes.MLIR (Word)
open Silmaril.SSA.RVSDG.NestedTheta.Petri (Finishes)

#eval layout
#eval mergeValues
#eval packets
#eval [0, 1, 2, 3].map sourceBudget
#eval (MLIR.CF.Example.runSource 19, MLIR.CF.Example.runCF 20, runNumbered 3)
#eval (MLIR.CF.Example.runSource 18, MLIR.CF.Example.runCF 19, runNumbered 2)
#eval (check MLIR.CF.Example.outerOverlap 0).isNone

example : Finishes (Silmaril.SSA.SeaOfNodes.Quads.Join.model model)
    (lower MLIR.CF.Example.plan) input (.cons (130 : Word width) .nil) :=
  (petri_finishes_iff MLIR.CF.Example.plan model input (130 : Word width)).mpr ⟨19, rfl⟩
```

`layout` reports `some (2, [1, 1], 1)` from the actual θ graph. The
two shared producers follow the inner γ, each inner child has one
producer, and the outer false child has one. The loop reaches merge
values `15, 65, 130` with packets `(1, 2, 15)`, `(1, 1, 65)`,
and `(0, 0, 130)` in tag, counter, and return-slot order. Source,
CF and θ return `130` at `19/20/3` and exhaust at `18/19/2`.
The overlap refusal still applies. This emitter uses the full carried
bank of the checked pure nested profile.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Numbered/Regression.lean)

### Outer reconvergence before the final join

`Nested.Shared.Outer.check` recognizes an additional nonempty common
tail on both outer routes. It cuts the two independently checked
routes at their first shared block and verifies that each original
block list is its ordered prefix followed by that same tail. The
coverage check counts every source block once and requires a nonempty
inner suffix exclusive to the outer true route. The original
`Shared.check` keeps its original inner-only profile and dependent
types. Both profiles reuse the routing and θ proofs.
[Recognizer and coverage certificate](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/Defs.lean) ·
[Inner-only API regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Compatibility/Regression.lean)

`Program.run_to_outer` identifies the selected outer predecessor's
complete bank. `Program.run_outer_suffix` charges one visit per shared
block and supplies the final merge bank. The numbered emitter reuses
the inner γ and its continuation, then compiles the outer suffix once
against the result wires of the outer γ. `outer_run` and `merge_run`
give the full banks at both boundaries. The suffix's operands read
the selected bank or its own earlier producers through the existing
typed quad compiler. `activation_run` gives the exact feedback or
exit packet. The existing finite-return, absence, and finite coloured
completion laws apply to this graph with separate witnesses.
[Source laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/Thms.lean) ·
[Numbered laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/Numbered/Thms.lean)

Build the two full imports below with `lake build --wfail` and a `+`
before each module name. Paste into `QuadNestedOuterSuffix.lean` and
run `lake env lean -DautoImplicit=false -DwarningAsError=true QuadNestedOuterSuffix.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example (input width)
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (model)
open Silmaril.SSA.SeaOfNodes.MLIR (Word)
open Silmaril.SSA.RVSDG.NestedTheta.Petri (Finishes)

#eval plan.outerSuffix.blocks.map Fin.val
#eval layout
#eval trace
#eval (outerValues, mergeValues, packets)
#eval [0, 1, 2, 3].map sourceBudget
#eval (runSource 25, runNumbered 3, runSource 24, runNumbered 2)
#eval (Outer.check crossesInnerPrefix 0).isNone

example : Finishes (Silmaril.SSA.SeaOfNodes.Quads.Join.model model)
    (lower plan) input (.cons (152 : Word width) .nil) :=
  (petri_finishes_iff plan model input (152 : Word width)).mpr ⟨25, rfl⟩
```

The actual θ has six vertices after the outer γ. Two are the new
suffix producers from blocks `10` and `11`. The final merge,
latch and route tag account for the other four. The inner structure
and outer false child have the same sizes as in the inner-only
fixture. The selected routes are inner true, inner false and outer
false, with pre-tail values `15, 73, 150` and post-tail values
`17, 75, 152`. The two feedback packets carry counters `2` and
`1`. Source and θ return `152` at `25/3` and exhaust at `24/2`.
The near miss sends the outer false route into an exclusive inner
prefix and is refused.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/Numbered/Regression.lean)

### Compare outer reconvergence in typed CF and numbered θ

`Shared.Outer.MLIR.CF.lower` uses the existing typed CF compiler on the
original checked table. `outer_arrival` gives the actual successor frame
from the selected predecessor block. Both outer predecessors target the
first original tail block with the full typed bank in register order.
`outer_arrival_sites_distinct` distinguishes the original predecessor
labels. CF frames carry the destination and its operands. The originating
block and outgoing slot are available through `Program.outerEdgeOccurrence`.
`from_header_eq_tail` connects these packets to execution from the header.
[CF laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/MLIR/CF/Thms.lean)

`Comparison.outer_arrival` matches the frame against the actual outer γ
output. `Comparison.latch_successor_at_activation` reads the numbered
activation's control port and carried data to recover the CF feedback
frame or typed exit frame.
`cf_returns_iff` and `cf_finishes_iff` relate finite CF results to numbered
returns and coloured completions with their own witnesses.
`cf_noFiniteReturn_iff` and `cf_noCompletion_iff` quantify over all finite
bounds or completions. CF uses one more visit than the source runner for
its synthetic return block, θ counts activations, and coloured completion
uses a finite firing sequence. The laws cover the admitted pure outer
profile with full banks.
[Comparison API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/MLIR/CF/Comparison/Thms.lean)

Build the two imports with `lake build --wfail`, prefixing each module
with `+`. Paste into `QuadNestedOuterCF.lean` and run
`lake env lean -DautoImplicit=false -DwarningAsError=true QuadNestedOuterCF.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Comparison.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Example
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example
  (runSource runNumbered)

#eval arrivals
#eval successors
#eval (runSource 25, runCF 26, runNumbered 3)
#eval (runSource 24, runCF 25, runNumbered 2)
```

The arrivals report `(predecessor, slot, target, result register)` as
`(6, 0, 10, 15)`, `(6, 0, 10, 73)` and `(7, 0, 10, 150)` for inner true,
inner false and outer false. The latch returns to header `1` twice,
passing `(counter, result register)` pairs `(2, 17)` and `(1, 75)`, then
exits with `152`. All three runners return `152` at `25/26/3` and exhaust
at `24/25/2`. The regression also derives finite coloured completion
from the actual CF result.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/MLIR/CF/Regression.lean)

### Read the explicit Φ at the outer tail

`Shared.Outer.MLIR.CF.Phi.readRows` reads the terminal operands of the
two emitted CF predecessor blocks at their original source successor
slots. `readRows_exists` proves that the admitted plan supplies both rows.
`Rows.view` uses `PhiView.ofBlockArgs` to transpose them into typed
destination slots. A row keeps the local CF variable indices, so an
index is interpreted in its own predecessor's post-body scope.
The two inner routes share the outer-true occurrence after the exclusive
inner suffix. An outer-false direct arrival uses slot 1 of the header's
conditional terminator.
[Φ view](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/MLIR/CF/Phi/Defs.lean)

`Rows.transfer_iff` uses the existing explicit-Φ latch law. The row reads
all operands from one post-body environment. `Rows.first_tail` proves
that the real first tail block sees the full bank, with the original
external arguments still in scope. `Rows.numbered_latch` identifies the
same packed bank in the actual numbered outer γ. The existing comparison
laws cover finite returns and absence in CF and the numbered θ with
independent budgets. This view covers the outer join of the admitted
full-bank profile.
[Correspondence laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/MLIR/CF/Phi/Thms.lean)

Build the two imports with `lake build --wfail`, prefixing each module
with `+`. Paste into `QuadOuterPhi.lean` and run
`lake env lean -DautoImplicit=false -DwarningAsError=true QuadOuterPhi.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Example (runCF)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example
  (runSource runNumbered)

#eval columns
#eval selected
#eval directSelected
#eval (runSource 25, runCF 26, runNumbered 3)
#eval (runSource 24, runCF 25, runNumbered 2)
```

The rows are keyed by `(6, 0)` and `(7, 0)`. The three selected banks
contain result-register values `15, 73, 150` and retain their other word
and `i1` slots. In the direct-edge variant the outer-false bank arrives
from `(1, 1)` with result-register value `75`. The original source, CF,
and θ runners return `152` at `25/26/3` and exhaust at `24/25/2`.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/MLIR/CF/Phi/Regression.lean)

### Reconstruct and validate the two outer-tail CF packets

The admitted outer join has two distinct predecessor blocks.
`Readback.predecessor_key_injective` specializes the coverage certificate
to those occurrences. `Readback.other_slot_excluded` inspects the raw
emitted successor and shows that a second slot of either predecessor
cannot enter the outer tail. In the direct-false fixture the header's
true slot targets the inner split and its false slot targets the outer
tail. The underlying pure quad CF emitter uses one final version map
for both arms of a conditional, so a repeated destination in that
emitter carries the same operand list on both arms.
[CF terminator emitter](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Diamond/MLIR/CF/Defs.lean)

`Readback.edge` recovers each actual typed CF edge from
`PhiView.toBlockArgs`. `edge_is_actual` gives equality of the whole
successor, including the destination and the ordered scoped operands.
`checkBanks_iff` characterizes validation of both complete value packets
in their respective post-body environments. `numbered_readBank`
identifies the reconstructed bank with the actual numbered outer γ
on a reached occurrence. The existing CF and numbered θ comparison
continues to provide finite-return and absence laws at independent bounds.
[Readback laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/MLIR/CF/Phi/Readback/Thms.lean)

Build the two imports with `lake build --wfail`, prefixing each module
with `+`. Paste into `QuadOuterPhiReadback.lean` and run
`lake env lean -DautoImplicit=false -DwarningAsError=true QuadOuterPhiReadback.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Readback.Example

#eval rebuiltBanks
#eval checks
#eval gammaMatches
#eval directTargets
```

The original 152 fixture gives result-register values `15` and `150`
at predecessor slots `(6, 0)` and `(7, 0)`. The packet check returns
`(true, false, false)` for the two source banks, the true bank with its
first two word slots reordered, and the two banks swapped between
predecessors. Both reconstructed banks match the actual γ output.
The raw direct-false successors target blocks `2` and `7`, in that order.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/MLIR/CF/Phi/Readback/Regression.lean)

### Round-trip the inner shared-tail packets

`Shared.MLIR.CF.InnerPhi.readRows` works on the routing certificate
shared by the inner-only and outer-reconverging profiles. It reads each
raw CF successor by its original block and outgoing slot, then checks
the common inner destination. `Rows.edge_roundtrip` reconstructs the
actual ordered, scoped operands through `PhiView.toBlockArgs`.
`Rows.bank_eq` proves that all operands read the same post-body
environment and reconstruct the full source prefix bank. `Rows.from_header`
and `Rows.first_tail` connect that packet to the actual first tail block.
[Inner-tail API](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/MLIR/CF/InnerPhi/Thms.lean)

`Rows.numbered_bank` reads the existing numbered inner γ at its
connection to the shared suffix. `inner_wiring` and `legacy_inner_wiring`
show that restoring the original continuation gives the exact two
existing emissions. The outer-profile finite-return and absence laws
still apply at their independent bounds.
[CF/θ comparison](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/MLIR/CF/Comparison/Thms.lean)

Build the two imports with `lake build --wfail`, prefixing each module
with `+`. Paste into `QuadInnerTailPhi.lean` and run
`lake env lean -DautoImplicit=false -DwarningAsError=true QuadInnerTailPhi.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Example (runCF)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example
  (runSource runNumbered)

#eval trace
#eval gammaMatches
#eval parallelColumns
#eval (runSource 25, runCF 26, runNumbered 3)
#eval (runSource 24, runCF 25, runNumbered 2)
```

The first two activations read seven-slot inner banks at `(3, 0)`
and `(4, 0)` with result values `7` and `36`. The outer bank then
arrives at `(6, 0)` with `15` and `73`. The third activation
bypasses the inner tail and arrives at `(7, 0)` with `150`.
Both inner arrivals match γ. In the inner-only direct fixture,
both CF slots of block `2` target the same inner-tail block.
They retain separate occurrence keys and carry the same post-body
operand list. The original run returns `152` at `25/26/3`
source/CF/θ fuel and exhausts at `24/25/2`.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/MLIR/CF/InnerPhi/Regression.lean)

### Observe the join packets in coloured markings

`Outer.Numbered.Petri.Boundaries.Thms` adds observations to the actual
numbered θ body. A typed `Cut` shares the emitted vertices and child
terms, and its observer reads the colours at the existing result wires.
The cut lifts legal prefix firings into the same continuation. The
outer witness has the γ output places marked. The inner witness is
inside the live selected outer-true child, with the outer γ still
waiting. The outer-false witness enters the actual bypass child
and reads `none` at the inner boundary.
[Typed marking cut](../../Silmaril/SSA/RVSDG/NestedTheta/Petri/Cut/Thms.lean) ·
[Quad boundary laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/Numbered/Petri/Boundaries/Thms.lean)

Both observations compare complete typed banks with the CF/Φ readback.
The fixture uses separate finite firing witnesses for each activation
boundary and for the whole θ's return. Source and CF bounds count block
visits, the numbered bound counts activations, and each legal firing
witness has its own length. The packets printed below come from the
existing CF/Φ fixture. The Lean example proves their marking witnesses
and the coloured completion with word `152`.

Build both imports with `lake build --wfail`, prefixing each module
with `+`. Paste into `QuadSharedPetriBoundaries.lean` and run
`lake env lean -DautoImplicit=false -DwarningAsError=true QuadSharedPetriBoundaries.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Boundaries.Example.Defs
meta import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered (petri_finishes_iff)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Petri.Example
  (activation completion)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.Numbered.Example (plan)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example (input width)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example (rows)
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.Outer.MLIR.CF.Phi.Example renaming rows → outerRows
open Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF (model)
open Silmaril.SSA.SeaOfNodes.MLIR (Word)

set_option maxHeartbeats 1000000 in
example : completion := by
  unfold completion
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨bank, marked, _, packet⟩ := outer_packet plan input (activation i) outerRows
    exact ⟨bank, marked, packet⟩
  · exact inner_waiting_packet plan input (activation 0) rows (by rfl)
  · exact inner_waiting_packet plan input (activation 1) rows (by rfl)
  · exact bypass plan (activation 2) (by rfl)
  · exact (petri_finishes_iff plan model input (152 : Word width)).mpr ⟨25, rfl⟩

#eval Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.Shared.MLIR.CF.InnerPhi.Example.trace
```

The first two activations read inner result slots `7` and `36` and
outer slots `15` and `73`. The third prints `none` at the inner
boundary and `150` at the outer boundary.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/Shared/Outer/Numbered/Petri/Boundaries/Regression.lean)

## Complete the emitted loop by coloured firing

The `Backends/Petri/Thms` import adds completion laws for the numbered
graph returned by `Backends.compile`. `NestedTheta.Petri.initial` puts
pending tokens on that graph's vertices. Its existing firing relation
uses the original typed input bank as the root colours. The result
decoder reads the single returned port with `get .head`.
[Firing model](../../Silmaril/SSA/RVSDG/NestedTheta/Petri/Defs.lean)

`Targets.petri_finishes_iff` relates complete output tuples to finite
source returns. `Targets.petri_firing_iff` gives the same result as a
reachable marking with the decoded word. `Targets.petri_no_completion_iff`
covers absence of a finite completion at every output. A firing trace
has its own length. The source, CF and θ bounds retain the meanings
given above. These laws concern existential finite completions of the
existing pure nested profile.
[Completion laws](../../Silmaril/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/DeadProducer/Iteration/Backends/Petri/Thms.lean)

Build both imports with `lake build --wfail` using a `+` before each
module name. Paste into `QuadNestedPetri.lean` and run
`lake env lean -DwarningAsError=true QuadNestedPetri.lean`.

```lean
module

import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Petri.Thms
import Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends.Example.Defs

open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Nested.MergePrune.Latch.DeadProducer.Iteration.Backends
open Silmaril.SSA.SeaOfNodes.Quads.Loop.Tail.Diamond.MLIR.CF.Example (input width)
open Silmaril.SSA.SeaOfNodes.MLIR (Word)
open Silmaril.SSA.RVSDG.NestedTheta.Petri (Step initial result)

private def firingModel :=
  Silmaril.SSA.SeaOfNodes.Quads.Join.model Silmaril.SSA.SeaOfNodes.Loop.MLIR.CF.model

private def targets : Targets Example.source 0 := ((compile Example.source 0).toOption).get (by rfl)

example : ∃ final, Relation.ReflTransGen (Step firingModel targets.numbered input)
    (initial firingModel targets.numbered) final ∧
    (result firingModel targets.numbered input final).map (fun packet => packet.get .head) =
      some (16 : Word width) :=
  (targets.petri_firing_iff input (16 : Word width)).mpr ⟨14, rfl⟩
```

The proof uses the fixture's source bound `14` to obtain a finite
firing witness through the actual emitted graph. The regression also
rules out a completion with word `17` at any firing length and checks
the original shape refusal.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Quads/Loop/Tail/Nested/MergePrune/Latch/DeadProducer/Iteration/Backends/Petri/Regression.lean)
