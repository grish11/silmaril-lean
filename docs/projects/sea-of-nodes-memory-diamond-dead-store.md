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
