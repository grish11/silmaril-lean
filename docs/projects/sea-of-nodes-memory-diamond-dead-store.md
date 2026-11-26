# Delete a Store overwritten on both diamond occurrences

Simple chapter 10 joins the incoming memory from a conditional Store
using a memory Φ. Its local Store-after-Store rewrite checks the same
pointer and field and the old Store's memory users. The chapter also
shows how a read before an overwrite can observe the earlier write.
[Pinned Simple memory Φ](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable) ·
[Pinned StoreNode rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[IR ’95 §§2.5 and 3.1](https://doi.org/10.1145/202530.202534)

`DeadStore.Prefixed` adds one native entry Store to the existing
memory diamond. The Store consumes the initial heap, and its whole
output heap enters the diamond. The guard is an evaluated Boolean.
Each Region occurrence names its own Store version within its original
arm and the intervening reader ports. The checker prepends the Store to
that arm's native table and invokes the straight-line elimination at
versions 1 and the nominated arm version plus 1. Both checks use the
entry Store's exact address port and validate concrete reader inequalities
at the given input.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Defs.lean) ·
[Straight-line verifier](sea-of-nodes-memory-dead-store.md)

Success returns a native diamond with the two checked arm bodies. The
proof uses `Merge.predecessor` and `Merge.slot` to select the corresponding
checked occurrence for each guard. The original suffix runs on the
same selected word and heap, and finite explicit-edge returns agree on
the word and entire final heap. The scope is one entry Store, one If,
and one Region in the initialized word-cell profile.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Thms.lean)

The fixture exercises both guard values in both predecessor orders.
The arms have different overwrite positions, reader ports, returned
words, and side writes. Missing the overwrite or reading the observed
cell in just one arm rejects the transformation. A separate rejection
co-locates the observed cell and a reader carried on a different port.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Regression'
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Regression
```

## Check the all-path join packets

The two-route entry cut uses a separate overwrite and reader certificate
for each Region occurrence. It permits a Load before the overwrite when
the certificate validates that Load's cell as disjoint at the typed
invocation. The entry Store may feed both arms. Each path must establish
its own overwrite, and the checker refuses the whole edit if either
path reads the old cell before the overwrite or lacks an overwrite.
[Pinned Simple memory Phi](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

`rewrite_arm_observations` proves equality for every ordered Load and
the full exported word and heap at each checked occurrence. The same
packet is latched at the corresponding Region input, leaving the
shared suffix's Load observations equal. `MemRef.CF.lower_join_eq`
runs each actual emitted arm from its own entry buffer and compares
the complete jump packet into the join. The entry buffers can differ
until the checked overwrite. The slot order and the CFG return and
full final buffer agree for both predicates, every CF budget and any
initial buffer at the checked input.
[Native theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Thms.lean) ·
[Emitted join theorem](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Discovery/MemRef/CF/Thms.lean)

The fixture reads the actual join packets for both guards and both
Region orders. It also checks that emission refuses an observing Load
or a missing overwrite on just one route.
[Runnable fixture](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

## Check a finite predecessor bank

`DeadStore.Finite.check preds store arm candidate input` uses the
existing nonempty quad predecessor table to index a bank of ordered
memory paths. The table position selects the path and its overwrite and
reader certificate. Several positions can carry the same predecessor
identifier. Each position gets its own check, and one refusal prevents
the entire cut. The binary diamond uses the same per-path checker.
[Predecessor table](../../Silmaril/SSA/SeaOfNodes/Quads/CFG/Defs.lean) ·
[Memory checker](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/Defs.lean) ·
[Pinned Simple memory Phi](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

At each selected position the proof preserves every ordered Load
readback and the entire word and heap packet. Any native continuation
receives that same packet. Reindexing the paths and certificates by
the same occurrence permutation gives the correspondingly reindexed
results. The scope starts with an admitted incoming position and its
full straight-line paths, at a scalar valuation accepted by all the
reader checks.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/Thms.lean)

The native fixture reads the packet from the existing straight-line
MemRef emitter for each of three paths, reverses their predecessor
order, and checks that a Load of the old cell on only the middle path
refuses. The same fixture exercises the whole switch CFG below.
[Runnable fixture](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Finite.Regression
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/Regression.lean
```

## Emit one MemRef switch and join

`DeadStore.Finite.MemRef.CF.lower` checks the finite certificate and
emits the original and edited typed CFGs. The entry uses the existing
`cf.switch`, with one `i64` case for each incoming position. The
`Fits` proof ensures every admitted `Fin` selector fits the width
without truncation. `dispatch_selector` proves the emitted switch
chooses its exact occurrence label. That label is keyed by position,
so repeated predecessor IDs keep separate arm blocks. The switch
default is unreachable at a typed selector.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/MemRef/CF/Defs.lean) ·
[Typed switch operation](../../Silmaril/SSA/MLIR/CF/SwitchAssert/Defs.lean)

The existing ordered scheduler executes the switch entry, one arm
and the shared continuation. The original entry runs the common
Store once. The arm passes its word as the join argument and threads
the entire MemRef buffer as state. Both emitted CFGs send the same
word and complete buffer to the join and return the same word and
buffer at every CF budget for the checked input and any initial
buffer. Three block ticks suffice.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/MemRef/CF/Thms.lean)

The regression checks all three selected slots, the actual join
packets and final buffers, and reversal with the selector transported
to its new position. An observing Load in the middle path refuses
emission. The continuation makes the selected word observable through
a side-cell Store.
[Runnable fixture](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/Regression.lean)

## Keep the typed entry prefix before the switch

`DeadStore.Finite.MemRef.CF.FinalEntry.lower` takes a one-based Store
nomination in the native entry table. It reuses `Static.Final.cut`,
which admits original argument address and data operands on the
nominated Store immediately before Return. The preceding typed
Loads and Stores execute in their original order in both emitted
CFGs. A retained Store can consume a loaded word or write the same
concrete cell as the nominated Store.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/MemRef/CF/FinalEntry/Defs.lean) ·
[Pinned Simple memory Phi](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

The entry keeps its scalar result and its exact switch occurrence.
Reapplying the removed Store to the optimized entry buffer recovers
the original entry buffer. The finite checker validates the overwrite
and reader evidence at each occurrence. The selected emitted arms
then send the same word and complete buffer to the join, and the
two CFGs agree on the native return for every CF budget and every
initialized buffer at the certified input.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/MemRef/CF/FinalEntry/Thms.lean)

The fixture keeps a Load-fed side write and an aliasing prefix write.
It reads the entry buffers, join packets and final buffers across all
three occurrences, including repeated predecessor IDs. A read of
the overwritten cell on the middle path refuses emission.
[Runnable fixture](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/Regression.lean)

## Keep certified trailing Loads before the switch

`DeadStore.Finite.MemRef.CF.LoadTail.lower` combines the typed
`Final.cutWith` prefix traversal with `Static.Final.LoadTail.checkTail`.
The nominated last Store takes its address and data from original
argument ports. Its suffix consists of a nonempty chain of
argument-addressed Loads and the original Return. The cut preserves
the admitted typed Load/Store prefix, the suffix's read order, and
the selected return wire. One concrete typed input validates every
suffix separation fact and every finite route certificate.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/MemRef/CF/LoadTail/Defs.lean) ·
[Pinned Simple memory Phi](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

The emitted entry word agrees for every initialized buffer. Reapplying
the removed write to the optimized entry buffer recovers the entire
original entry buffer. The shared switch emitter preserves the selected
occurrence and the exact join frame, including its word and full
buffer. Both CFGs return the same native word and buffer at every
common CF budget.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/MemRef/CF/LoadTail/Thms.lean)

The fixture returns a trailing Load from the actual compiled entry
and checks every selected join packet and final buffer with duplicate
predecessor IDs. It covers refusal for a missing separation fact, two
distinct ports naming the same cell, and a middle route that reads the
old cell before its overwrite.
[Runnable fixture](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Finite/Regression.lean)

## Bypass a single-user Store inside one arm

`DeadStore.SingleUser.rewrite graph slot version` applies Simple chapter
10's direct Store bypass to one arm of the native memory diamond. The
Region slot selects the actual predecessor and the one-based version is
local to that arm. The existing linear checker reads the named memory
operands, checks the same typed address port, and requires the following
Store to be the sole user. The diamond census reports an arm Return
as the memory Phi input at that precise slot.
[Pinned Simple StoreNode rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[Pinned Simple memory Phi](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable) ·
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/SingleUser/Defs.lean)

An arm can have several Loads on its current version, and its Return
exports the current version exactly once at its Region occurrence.
The other arm has its own version namespace. The suffix receives
only the selected export, so no arm snapshot reaches the suffix
separately from that Phi. A second Load user or a version exported
without the required overwrite refuses the edit.

The proof preserves the Region ordering, every Load in each arm and the
suffix, and the exact latch observation at either slot. The emitted
MemRef CFGs enter the same arm slot and send the same jump frame, word,
and complete buffer to the join. Both runs agree on the returned word
and full buffer for either predicate and every CF budget, typed
valuation, and initialized buffer. The fixture runs both guard values
in both Region orders, reads the actual join packets and final buffers,
and exercises the observer and export refusals.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/SingleUser/Thms.lean) ·
[Runnable fixture](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/SingleUser/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.SingleUser.Regression
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/SingleUser/Regression.lean
```

## Discover both overwrites

`DeadStore.Discovery.rewrite source input` infers the two arm witnesses.
For each Region input occurrence it follows `Merge.predecessor` to the
actual arm, prepends the entry Store, and runs the existing straight-line
reader and overwrite searches. These collect Load ports up to the first
Store on the entry Store's original address wire. The discovered overwrite
version is converted back to the arm's numbering by subtracting the
prepended version. Each arm has its own reader list and overwrite version.
[Discovery definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Discovery/Defs.lean) ·
[Straight-line reader discovery](sea-of-nodes-memory-dead-store.md#infer-the-reader-certificate)

The original two-route checker validates the reader ports against concrete
cells at a single typed input. Success identifies the inferred witness and
checked output for each occurrence, and preserves and reflects the returned
word and entire final heap for either guard at that input and any initial
heap. The common suffix receives the selected arm's result. The scope is
the initialized diamond with one entry Store and an evaluated Boolean.
[Discovery theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Discovery/Thms.lean)

The runnable fixture prints `(some (2, 1), true)` with the false predecessor
first. The pair gives the arm-relative overwrites at a disjoint input. The
Boolean records that the automatic rewrite refuses when the false arm's
reader aliases the written cell, even though the true arm still passes.
The fixture also reverses the predecessor order and checks the exact word
and full heap for both guards at a shared disjoint input.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.Forwarding.Disjoint.Regression'
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Compare the emitted MemRef CF diamonds

`DeadStore.Discovery.MemRef.CF.lower source input` first checks discovery
for both routes. On success it emits the original and optimized typed
ordered CF artifacts. The original entry runs the lowered Store before its
`cf.cond_br`. In both artifacts the selected arm passes its word to the
shared join, and the ordered runner threads one initialized rank-one
`memref<nxi64>` buffer through the entry, selected arm, and suffix. The
scalar input used to check aliasing is retained with the emitted pair.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Discovery/MemRef/CF/Defs.lean) ·
[Existing ordered CF runner](../../Silmaril/SSA/MLIR/CF/Ordered/Defs.lean) ·
[Existing MemRef lowering](sea-of-nodes/memory/sea-of-nodes-memory.md#one-initialized-rank-one-memref) ·
[Pinned CF operations](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/include/mlir/Dialect/ControlFlow/IR/ControlFlowOps.td)

Both entry terminators select the same original Region slot. The proof
accounts for one block step each for entry, the selected arm, and the
join. The reader observes `none` before three steps and the source
word and full final buffer at every sufficient budget. Equality holds
for either predicate and every initial buffer at the checked input.
The budget counts CF blocks, with each ordered MemRef body executing
inside its block step.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Discovery/MemRef/CF/Thms.lean)

With the false predecessor first, the executable fixture reads back
both emitted slot numbers and all four final cells for both predicates.
It checks a short budget and a swapped predecessor order. When the
false route's incoming reader aliases the entry Store's cell, discovery
returns no artifacts.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.MLIR.MemRef.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Regression'
```

### Reuse the emitted entry buffer

`entryTransition` reads the destination frame and entire post-entry buffer
from the actual ordered CF entry evaluation. `lowerDiamond_entryTransition`
identifies that buffer with the optional entry table's native denotation
at the same typed scalar input. `lowerDiamond_run_seeded` then relates a
run with the entry table to a run of the bare diamond initialized with
that buffer. Both runs use the same predicate and scalar input. The law
compares whole-buffer return observations at every CF block budget.
[Entry and run theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Discovery/MemRef/CF/Thms.lean)

The runnable fixture emits two Stores as a straight-line entry table. The
false arm reads `11` from the first write at disjoint addresses. When the
addresses coincide it reads `99` from the second write. Both executions
read back the entry buffer and compare the returned word and every final
cell with the seeded run. The true arm also runs at the disjoint input.
[Executable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean) ·
[Pinned Simple memory chain](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#one-memory-value)

Native `Prefixed` carries one entry Store, and the automatic checker
returns a bare diamond on success. The entry-buffer law supports backend
composition with any admitted straight-line entry table. Repeating native
deletion would require a representation and checking law for the entry
Stores remaining after a successful deletion.

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Delete a Store within a two-Store entry

`DeadStore.Entry.rewrite entry input` accepts a native straight-line entry
table with exactly two Stores. It checks Store version 1 for deletion and
version 2 for the overwrite. The Stores must address the same original
port. The straight-line discovery and validator require each Load between
them to read a concretely distinct cell at the supplied scalar input.
The checked edit keeps the Loads and second Store in order with their
original operands and renumbers the live memory edges.
[Entry definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Defs.lean) ·
[Pinned Store user check](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65)

`Entry.lower graph entry input` emits both artifacts on success and
returns `none` on refusal. They use the same diamond, original incoming
slots and checked scalar input. The entry-transition theorem equates their
destination frames and entire buffers. The execution theorem equates
their returned word and full final buffer for either predicate and any
initial buffer. Both artifacts use three CF block steps because the edit
removes a MemRef operation inside the entry block. A shorter budget gives
no return observation in either artifact.
[Entry theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Thms.lean)

The runnable fixture retains a Load whose result is the second Store's
operand. At the disjoint input both emitted entries write `3`, and both
predicates agree on the word and all four final cells. At the aliasing
input the Load reads `99` from the first Store and the checker refuses
before emission. The original emitted program returns `99` in that case.
This edit establishes the overwrite within the entry table.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

## Select a Store in a longer entry table

`Entry.rewriteSelected entry version input` takes the one-based original
Store version to remove. The existing straight-line search finds the
first later Store on the same original typed address wire. The checker
validates each intervening Load's inferred reader obligation against the
concrete input cells. Refusal returns `none`. On success the result gives
the two original versions, the certificate, and the edited table. Its
operation theorem counts one deletion and keeps the operands and relative
order of all retained Loads, Stores, and the entry Return.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Defs.lean) ·
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Thms.lean) ·
[Pinned Simple Store user check](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65)

`Entry.lowerSelected` shares the two-Store entry emitter. The #3895
entry-buffer theorem gives equality of the emitted successor frame and
whole entry buffer. Both CFGs preserve the word and entire final buffer
at either predicate and arbitrary initial buffer at the checked input.
Both need three CF block steps, independent of which Store is removed
inside entry. The scope is one deletion with an overwrite in the same
entry table.
[Entry buffer law](#reuse-the-emitted-entry-buffer)

The three-Store fixture selects version 2, checks the exact edited table,
and runs both emitted artifacts. The false arm preserves `11` in the
cell written by the retained side Store. A second table checks deletion
with the side Store between the selected version and its overwrite. When
the intervening reader aliases, the original emitted artifact returns
`99` and the checker refuses to emit an edited pair.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.MLIR.MemRef.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.MLIR.MemRef.CF.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.MLIR.Finite.Regression'
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Repeat checked deletions within the entry

`Entry.lowerRepeated graph entry input` returns the final native entry,
the exact deletion count, and both emitted MemRef CFGs. It uses the same
checked scalar input throughout. After each deletion the native pass
renumbers memory edges and rediscovers reader obligations. It scans the
current one-based Store versions oldest first and checks the first later
same-wire overwrite for each candidate. Refused candidates leave later
candidates available. When no candidate passes, the pass keeps the
current table and all earlier deletions. An initial refusal of every
candidate yields an emitted pair with zero deletions.
[Native repeat pass](sea-of-nodes-memory-dead-store.md#repeat-checked-deletion) ·
[Entry definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Defs.lean)

The pass exhausts the checked selector and preserves the order and typed
operands of every retained operation. By the entry-buffer law, both
artifacts produce the same successor frame and the same full buffer for
either predicate and every initial buffer. They return the same word and
whole final buffer at every sufficient CF budget. Both need three block
steps, since all deletions occur inside the entry block. Shorter budgets
produce no return observation. The scope is overwrites within the ordered
entry table of the initialized diamond.
[Entry-buffer law](#reuse-the-emitted-entry-buffer) ·
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Thms.lean)

The runnable fixture deletes Store 1 using Store 2, then deletes the
renumbered Store 2 using Store 3. The false arm leaves the surviving side
Store's value `11` in the final buffer. With a concrete reader alias the
first deletion is retained and the later one is refused. Both emitted
CFGs still return `99` and agree on every final cell.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

## Follow entry deletion with a two-route overwrite check

`Entry.Composition.lower graph entry input` runs the repeated entry-local
pass first. The handoff recognizes a residual table consisting of one
Store with an original address and word argument, followed by Return.
Its typed adapter preserves the heap at the entry boundary, where the
entry's returned word is discarded. The all-path checker then discovers
both overwrite versions and reader certificates on the current entry and
the actual incoming Region slots. Each route is checked at the same
scalar input. A residual entry outside this shape, or a refusal on either
route, keeps the emitted result of the first pass.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Defs.lean) ·
[Pinned Simple Store rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[Pinned Simple memory Φ](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

The result reports the entry-local deletion count and whether the
all-path deletion succeeded. The actual MemRef CFGs agree on the returned
word and whole final buffer for either predicate and any initial buffer
at the checked input. Both return at three CF block steps, and smaller
budgets have no return observation. A successful all-path deletion can
change the entry buffer before the selected arm overwrites the cell.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Thms.lean)

The runnable disjoint fixture commits both stages and compares every
final cell under both predicates. At the aliasing input only the false
route observes the residual Store. The all-path check refuses, and the
already edited entry still supplies the optimized artifact. That run
returns `99`. A residual entry containing a Load also fails the adapter's
shape check.
[Runnable example](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Keep an ordered chain of residual entry Stores

`Entry.Composition.Retained.lower graph entry version input` runs the
existing entry-local pass. The next stage recognizes a nonempty residual
chain of argument-addressed Stores of argument words, followed by Return.
The version is one-based in that residual table. The checker compares the
nominated cell with the cells written strictly after it. The retained
prefix establishes the same heap before nomination and can include a
write to that same cell. The proof moves the nominated write over the
disjoint suffix only. The emitted entry keeps the exact prefix and suffix,
in order, including retained writes to coincident cells. The residual
chain admits only Stores before Return. Every Load before the nominated
Store's overwrite on either route must pass the existing reader checker
at the same input.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Defs.lean) ·
[Pinned Simple Store user check](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[Pinned Simple memory Φ](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

The existing discovery checks the actual Region slots, including the
original address wire at each overwrite. After a successful check, the
optimized entry forwards the original Region frame and the entire buffer
produced by the retained table. `Edit.retained` carries that native table
with consecutive memory versions and the original Return operand. The
original and optimized CFGs return the same word and all final cells for
either predicate and any initial buffer at the checked input.
Three CF block steps suffice for both artifacts. A shape, cell, or route
refusal keeps the emitted entry-local result.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Thms.lean)

The runnable fixture nominates the middle Store in a three-Store residual
table. The first and last Stores use distinct ports that resolve to the
same cell. Both routes read the last write, `33`, from that cell. Another
valuation aliases the prefix Store and the nominated Store through
distinct address ports. The prefix alias survives the entry-local pass,
which finds overwrites by wire identity. The all-path step accepts and
both emitted CFGs agree on the word and every final cell under both
predicates. Placing the aliasing Store in the suffix refuses the all-path
step even though both route checks pass. The entry-local deletion stays
committed. The two-Store fixtures also check a reader alias confined to
the false route.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Keep an ordered suffix of entry Loads and Stores

`Entry.Composition.Retained.Load.lower graph entry version input`
runs the entry-local pass, then checks a one-based Store version in
the residual table. The supported entry has an argument-Store prefix
up to and including the nominated Store. Its suffix is an ordered
sequence of Loads and Stores ending in Return. Every suffix access
must use an original address argument whose concrete cell differs from
the nominated cell. Store data and Return can use any in-scope word,
including earlier Loads. The cut removes one Store and preserves the
order and scalar operands of every retained operation.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Defs.lean) ·
[Pinned Simple Store user check](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[Pinned Simple load/store order](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#executing-the-graph)

Each checked Load binds the same word in both executions. Each checked
Store uses the same live scalar bindings, and its disjoint update
commutes with the nominated write. The induction maintains that replaying
the nominated Store reconstructs the source heap at every suffix step.
The existing discovery then checks the overwrite and intervening readers
independently at both Region occurrences.
The optimized MemRef entry emits the original successor frame and the
retained table's full buffer. Both emitted CFGs return the same word and
all final cells at any initial buffer and either predicate at the checked
input. Three CF block steps suffice for both artifacts.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Thms.lean) ·
[Pinned Simple memory Φ](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

The original one-Load fixture still runs. The two-Load fixture returns
the older binding at the native entry boundary and uses the newer binding
in a retained Store. Both emitted routes read that Store's value. When
only the later Load aliases the nominated cell, the suffix check refuses
even though both route checks pass. The earlier entry-local deletion stays
committed and the emitted CFGs preserve the observed `99`.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Kill the nominated write inside the entry

`Entry.Composition.Retained.Load.lowerOverwrite graph entry version input`
runs the same entry-local cleanup, then checks the one-based Store version
in the current table. It scans up to the first later Store whose original
address port resolves to the nominated cell. A Load of that cell before
the overwrite refuses the edit and keeps the earlier cleanup. The prefix
through the nominated Store consists of argument-addressed Stores of
argument words. The checked interval also uses original address ports.
A retained Store can use a word computed by an earlier Load. Simple’s
local Store rule checks that the pointer nodes are identical and that the
earlier Store has no other users. This fragment checks concrete cell
equality at the supplied typed input and scans the ordered access path
for a reader before the overwrite.
[Pinned Simple Store user check](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[Pinned execution order](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#executing-the-graph)

Before the overwrite, disjoint Loads bind identical words and disjoint
Stores commute with the nominated write. The first same-cell Store
therefore uses the same operand and restores whole-heap equality. Every
remaining operation runs on equal states. The native cut retains scalar
origins and operation order and reconnects the memory versions. Both
emitted CFGs keep the original diamond and agree on the successor
occurrence, entry buffer, returned word and all final cells at any
initial buffer, either predicate and every CF budget. Each takes three
CF block steps to return. The disjoint-suffix and two-route check remains
available through `Load.lower`. This check does not resolve dynamic addresses.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Defs.lean) ·
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Thms.lean)

The runnable regression removes an earlier same-wire duplicate, then
deletes the nominated write despite the next overwrite using a different
port. The overwrite copies a loaded word and a subsequent same-cell
Load feeds a retained Store. The false arm reads the overwritten cell
without writing it. Switching the first Load to the aliasing port
refuses the second deletion and preserves the observed `99`.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Emit the same entry edit for multiple valuations

`Entry.Composition.Retained.Load.Static.lower cells graph entry version facts prior`
emits the original and optimized MemRef CFGs from the native table and typed
address facts alone. The contract anchors the existing disjointness
certificate at the nominated Store's original address port and lists ports
that must denote that same cell. The anchor is its own alias. The ordered
check needs explicit disjointness for every access before the first proven
same-cell Store. Missing facts and contradictory classifications refuse
the cut. An invocation can validate its concrete addresses separately
with `AddressContract.check`.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Static/Defs.lean) ·
[Pinned Simple chapter 10 Store rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65)

`cut_agrees` reduces an accepted static edit to the exact existing concrete
cut at every satisfying valuation. Its proof uses the original first-overwrite
theorem to preserve scalar operands, access order, and the whole heap.
The emitted pair shares the original diamond. Both artifacts agree on the
entry successor packet and buffer, and on the returned word and every final
cell at either predicate, every initialized buffer and every CF budget.
All address facts refer to original typed address ports.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Static/Thms.lean)

The optional prior edit uses the existing same-wire checker with an empty
reader list. It is checked independently of the address contract. Nominate
the second edit's one-based Store version in the table after that cleanup.
Refusal leaves that table in the optimized artifact. The runnable example
executes the same pair at two valuations with different cells and words.
A pre-overwrite Load of a must-alias cell refuses the second edit while
keeping the first.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Transport the contract along typed entry maps

`AddressContract.transport` uses the memory-diamond institution's
`PortMap` to rename the nominated address and both fact lists. It refuses
identifying a required disjoint port with the anchor or any of its listed
aliases. It permits identifying two must-alias ports. A target invocation
passes the transported contract exactly when its pulled-back source
valuation passes the original contract.
[Typed entry maps](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/Institution/Defs.lean) ·
[Transport definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Static/Reindex/Defs.lean)

For a successful source cut, `cut_transport` maps the nominated Store and
each checked access through the same typed map. The first overwrite stays
at the same version, and the retained table is the exact original edit with
renamed entry uses and the same memory edges. Apply this to the current
entry table after any earlier cleanup. `lower_observations` uses the
existing native reindexing laws and the static MemRef emitter to compare
the re-emitted optimized CFG with the source artifact at the pulled-back
invocation. It proves equality of the entry successor packet and buffer,
and of the returned word and every final cell for either predicate, any
initialized buffer and every CF budget. The theorem compares execution
observations across the typed interfaces.
[Transport theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Static/Reindex/Thms.lean) ·
[Pinned Simple chapter 10 Store rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65)

The regression swaps two address ports and runs the actual emitted pair.
Identifying the two must-alias ports gives the same observations, while
identifying the required disjoint port with the anchor refuses transport.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Check a sequence of static entry cuts

`Entry.Composition.Retained.Load.Static.Sequence.lower graph entry plan input`
validates every step's typed address contract at this invocation. The plan
is a list of one-based Store nominations and contracts. `Plan.rewrite`
folds the existing first-overwrite check over the native entry tables,
using the table produced by the preceding steps. A failed contract or cut
returns `none` for the entire request. An empty plan emits the original
entry on both sides.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Static/Sequence/Defs.lean) ·
[Pinned Simple chapter 10 Store rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65)

A successful fold removes exactly one Store per step and preserves the
order and operands of every retained operation. The existing MemRef
emitter lowers the original and final tables with the same native
diamond. The emitted entries forward the same successor packet and full
buffer. At either predicate and any initialized buffer, both CFGs return
the same word and every final cell for every CF budget. Three block
steps suffice for each artifact. A common typed port map transports a
successful plan's contracts and exact final table using the single-cut
transport law.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Static/Sequence/Thms.lean)

The regression deletes Stores to two different cells. The Load between
the second nomination and its overwrite still reads the first cell and
supplies the retained Store operand. Reusing the second Store's original
version after the first deletion rejects the entire sequence. The
fixture also runs the transported plan through the MemRef CFGs after a
typed address-port swap. This is an explicit plan over ordered native
diamond entries, with the pinned Store rule as its source reference.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Discover a static entry plan

`Static.Sequence.Search.find entry contracts` tries the current one-based
Store versions in ascending table order. At each version it tries the
supplied typed contracts in list order. Every attempt uses the existing
first-overwrite checker, including its check for a Load that observes the
nominated cell before the overwrite. `discover` restarts this search on
each edited table and records the resulting versions in a replayable
`Sequence.Plan`.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Static/Sequence/Search/Defs.lean)

Simple chapter 10's `StoreNode.idealize` examines the previous memory
Store, requires the same pointer node and field, and checks for other
users before bypassing the earlier write. The correspondence here is
bypassing an unobserved overwritten Store on a memory chain. This
ordered-table finder checks supplied cell facts and intervening Loads,
and retries by scanning the current table after each edit.
[Pinned Simple chapter 10 Store rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65)

`Search.lower` validates all supplied contracts at the invocation. A
false contract yields `.error .invalidContracts`. A valid invocation
with no eligible cut yields `.ok` with an empty plan and an unchanged
entry. Each accepted cut decreases the Store count by exactly one, so
the original Store count suffices to exhaust the search. Exhaustion
means every remaining version and supplied contract pair fails this
first-overwrite checker. The emitted pair is exactly the result of
replaying the discovered plan through `Sequence.lower`. The actual
MemRef CFGs agree on the successor packet and full entry buffer, and on
the returned word and every final cell for either predicate, any
initialized buffer, and every CF budget.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Static/Sequence/Search/Thms.lean)

The fixture discovers two cuts at current versions `[1, 1]`, preserving
a retained Load after the first overwrite. A must-alias Load blocks
another fixture after its first cut, and both CFGs return the observed
`99` with matching full-buffer readback.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Infer equality-only contracts from Store operands

`Static.Sequence.Search.Inference.inferContracts entry` reads the typed
Store operands and emits one contract per address argument in first
occurrence order. Each contract relies on the checker's reflexive
must-alias for its own port, with empty disjointness and alias lists.
When a typed entry map routes two operands to the same port, the
reindexed table exposes that shared identity to inference.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Static/Sequence/Search/Inference/Defs.lean)

The native entry table uses address arguments, and Load produces a word.
The table has no closed address constants or producer of static
disequality evidence. Different argument ports can denote the same
cell, so their relationship stays unknown. Callers can still supply
explicit disjointness contracts to `Search.lower`. The source
correspondence is the same-pointer test in Simple chapter 10's
`StoreNode.idealize` and its check for other observers before bypassing
a Store.
[Pinned Simple chapter 10 Store rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65)

Lean proves that all valuations satisfy the inferred contracts.
`Inference.lower` supplies them to the existing `Search.lower`.
Its replay and exhaustion guarantees range over the inferred contracts
and the first-overwrite checker. The actual original and optimized
MemRef CFGs agree on the successor packet, entry buffer, returned word,
and every final cell for either predicate, every initialized buffer, and
every CF budget.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Retained/Load/Static/Sequence/Search/Inference/Thms.lean)

The runnable fixture discovers two cuts at version `4` after successive
renumbering. A same-port Load keeps the Store it observes live, and a candidate
with an intervening symbolic Store remains blocked even at a valuation
where the addresses differ. A separate routed fixture discovers a cut
after two Store operands are routed to the same typed port.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Check a same-port two-route cut for every valuation

`Entry.Composition.Static.lower cells graph entry` checks a current
singleton entry Store followed by Return. It reuses the existing
occurrence-indexed overwrite discovery. Each witness must name an
overwrite on the nominated Store's original typed address port and
have an empty reader list. A Load before the overwrite requires a
reader obligation and therefore refuses this all-valuations cut.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Static/Defs.lean) ·
[Pinned Simple chapter 10 Store rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[Pinned Simple memory Φ](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

A successful static rewrite replays through the existing concrete
checker at every typed valuation with the same witnesses and graph.
The actual emitted CFGs select the same entry successor packet and
agree on the returned word and entire final buffer for either
predicate, every initialized buffer and every CF budget. Before the
selected arm overwrites the cell, the original entry still exposes
the removed write and the optimized entry forwards the input buffer.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Static/Thms.lean)

The fixture explicitly supplies the singleton table left by equality-only
entry discovery. Its surviving Store moves from version two to one.
It exercises both occurrence orders, then runs the same emitted pair
under different predicates and valuations. A read of the nominated cell
on one route blocks the cut. A read through a different symbolic port
also blocks it, even at a valuation where the concrete checker can
certify disjointness. The API checks one supplied table.
[Staged entry and route discovery](#compose-equality-only-entry-discovery-with-the-two-route-cut)
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Compose equality-only entry discovery with the two-route cut

`Entry.Composition.Static.Staged.lower graph entry input` runs
equality-only discovery and passes its exact residual table to the
static singleton check. The result reports `entryNotSingleton`,
`routesRefused`, or `applied`. Both refusal outcomes use the actual
entry-only artifact. Success takes the optimized artifact from the
two-route emitter while keeping the original artifact from the first
emitter. Both stages use identity of the original typed address ports.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Static/Staged/Defs.lean)

`lower_checked` replays the entry plan through the explicit sequence
checker. On success it identifies the route emitter's original artifact
with the entry emitter's optimized artifact and reuses the existing
two-occurrence check. `lower_observations` compares the original and
final emitted CFGs at either predicate, every typed valuation,
every initialized buffer, and every CF budget. The successor packets
and final return and full buffer agree. When the second cut succeeds,
the entry buffers can differ until the selected arm overwrites the cell.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Static/Staged/Thms.lean) ·
[Pinned Simple chapter 10 Store rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[Pinned Simple memory Φ](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

The fixture passes the original two-Store table to the staged driver.
The second Store moves to version one before the two-route check.
Both Region orders run through the actual emitted CFGs. A one-route
read blocks the second cut and keeps the first, and a larger residual
table reports its own refusal while preserving both earlier deletions.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Keep the prefix before the final Store

`Entry.Composition.Static.Final.lower cells graph entry version` takes
the current native entry table and a one-based Store nomination. The
selected Store must use original address and word arguments and be
immediately followed by Return. The cut preserves every earlier native
Load and Store, their scalar operands and order, and the Return's word
wire. The current table may be the residual of entry-only discovery.
The original `Static.Staged.lower` uses the singleton emitter.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Static/Final/Defs.lean)

The source entry buffer is the nominated write applied to the full
retained prefix buffer. The optimized entry passes that prefix buffer
to the selected arm. The existing static two-occurrence check requires
a same-port overwrite and empty reader obligations on each route, and
its proof applies to that entire prefix buffer. Earlier prefix stores
can alias the nominated cell. The emitted CFGs select the same
successor packet and agree on the return and every final cell for either
predicate, every typed valuation, every initialized buffer, and every
CF budget. Three steps suffice for both CFGs.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Static/Final/Thms.lean) ·
[Pinned Simple chapter 10 Store rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[Pinned Simple memory Φ](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#memory-is-an-ssa-variable)

In the fixture the retained entry Load feeds an earlier Store. Both
routes read the result after overwriting the nominated cell. A second
valuation makes the two entry Store addresses alias and still accepts
the same cut. A pre-overwrite read of the nominated cell on one route
refuses the two-route cut.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Discover the final Store after entry discovery

`Entry.Composition.Static.Final.Staged.lower graph entry input` runs
the equality-only entry pass first. It takes the Store count of the
actual resulting table and checks that version with `Final.cut`.
`find_eq_some_iff` proves that discovery returns exactly the eligible
one-based version. The eligible shape is an argument-addressed Store
of an argument word immediately before Return.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Static/Final/Staged/Defs.lean)

The result distinguishes `noFinalCandidate`, `routesRefused version`,
and `applied version artifacts`. Both refusal outcomes keep the
entry-only emitted pair. On success, the final pair uses the original
artifact from entry discovery and the optimized artifact from
`Static.Final.lower`. The replay theorem checks the discovered entry
plan, the nomination on its exact residual table, and the equality
of the intermediate artifacts. Both stages use the existing typed
same-port and reader checks.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Static/Final/Staged/Thms.lean) ·
[Pinned Simple chapter 10 Store rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65)

The actual original and final MemRef CFGs agree on the successor
packet, returned word and entire final buffer for either predicate,
every typed valuation, every initialized buffer, and every CF budget.
The optimized entry forwards the retained prefix buffer before the
selected arm overwrites the nominated cell.

The runnable fixture starts with three Stores and removes the first.
The final Store shifts from version three to two, and both arms
observe the retained prefix Store. A pre-overwrite read on one route
keeps the first cut and refuses the second. A trailing entry Load
keeps the first cut and reports that the residual has no final
candidate.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Retain certified Loads after the last Store

`Static.Final.LoadTail.lower graph entry input facts` is the opt-in
staged driver for an argument-Store prefix followed by a nonempty
chain of argument-addressed Loads and Return. It runs equality-only entry
discovery first, then checks the last Store in the actual residual
table. The existing disjointness certificate must name that Store's
port and cover every reader. The driver validates the supplied facts
at the invocation. A missing or false fact, ineligible shape, or
route refusal keeps the exact entry-only emitted pair.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Static/Final/LoadTail/Defs.lean)

The existing typed suffix cut reconnects memory while keeping the
Load and Return wires. Every retained Load sees the same word before
and after the cut. Suffix replay preserves the exported entry word
and recovers the original entry heap by applying the removed write
to the retained heap. The static two-route checker then requires the
same-port overwrite and an empty reader list on each Region
occurrence. The actual emitted CFGs agree on the successor packet,
returned word, and full final buffer for either predicate, each
satisfying typed input, every initialized buffer, and every CF budget.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Static/Final/LoadTail/Thms.lean) ·
[Pinned Simple chapter 10 Store rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65)

The fixtures export either of two retained Loads from the entry
body. The native entry has a single Return word and no scalar
combining operator. `entryWord` reads the selected value from the
actual emitted code, and the separate CF runner exercises the
complete diamond. The CF entry forwards the buffer with the
selected successor packet. A later read of the nominated cell or
a later reader with missing or invalid separation keeps the exact
first optimized artifact.
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```

## Preserve one certified Store and its trailing Loads

`Entry.Composition.Static.StoreTail.lower graph entry version input facts`
runs equality-only entry discovery and takes a one-based nomination on
the actual residual table. The nominated Store uses original address and
word arguments and is followed by one argument-addressed Store, an
optional chain of argument-addressed Loads, and Return. The prefix may
contain Loads. A retained Store can therefore use the word of a preceding
Load through its original typed scalar wire. The concrete mixed-suffix
checker above requires an argument-Store prefix.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Static/StoreTail/Defs.lean)

The certificate names the nominated cell and covers the retained Store
and every trailing reader. Its concrete validation supplies separation.
The existing suffix replay commutes the nominated write with the
retained Store and preserves the Load bindings. The typed cut keeps
all other operations and their operands in order. The static
two-occurrence checker still requires same-port overwrites and empty
reader obligations. The actual MemRef CFGs agree on the successor packet,
return and full final buffer for either predicate and every initial
buffer and CF budget at a supported invocation. The emitted entry preserves
its scalar result and sends the retained buffer to the selected arm.
Reapplying the deleted write to that buffer recovers the original entry
buffer. Refusal preserves the exact entry-only artifact.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Entry/Composition/Static/StoreTail/Thms.lean)

Simple chapter 10 folds consecutive same-pointer Stores when the earlier
one has no other user. This fragment relates that memory-chain obligation
to a certified commute across an independent retained Store before a
two-route overwrite. The fixture retains the Store's Load-produced
operand and observes its value through both emitted routes. Missing
coverage, equal runtime cells and a branch that reads before its
overwrite all preserve the first optimized artifact.
[Pinned Simple Store rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[Memory coverage ledger](sea-of-nodes/coverage.md) ·
[Runnable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean)

```sh
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/Diamond/DeadStore/Regression.lean
```
