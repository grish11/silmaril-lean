# Delete a checked overwritten Store

In Simple chapter 10, `StoreNode.idealize` bypasses an earlier Store to
the same pointer and field when the earlier memory node has no other
uses. The chapter also shows a Load that must observe a value before a
later Store, and why effect sharing across control paths can create an
extra write. This formalization uses the admitted straight-line native
`Memory.Graph` table and its coherent, latest-version memory edges.
[Pinned StoreNode implementation](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L74) ·
[Pinned chapter 10 examples](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/README.md#local-memory-optimizations) ·
[IR ’95 §2.5](https://doi.org/10.1145/202530.202534)

Nominate two one-based Store versions in the original table. The checker
requires both Stores to use the same original typed address port and
finds the overwrite strictly after the Store to delete. Every intervening
Load needs a covered reader port and a concrete cell inequality from the
existing `Disjoint.Certificate`. A same-wire Load fails the static check.
The invocation checker rejects coinciding cells on different ports.
Intervening Stores remain in order with all their operands.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Defs.lean) ·
[Address certificate](../../Silmaril/SSA/SeaOfNodes/Memory/Forwarding/Disjoint/Thms.lean)

The rewrite removes the first nominated Store from the native graph and
reconnects its suffix with the new live memory versions. Its scalar
ports stay in scope because a Store produces only memory. The proof
tracks equal heaps outside the observed cell and equal scalar locals
through the gap. The checked overwrite restores equality of the entire
heap. The explicit-edge correspondence then gives preservation and
reflection of the returned word and whole final heap.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Thms.lean)

The fixture restores the initial value after logging a disjoint read.
If the reader aliases the removed Store's cell, deleting that Store
would change both Return and the logging cell. The checker rejects that
input. It also rejects missing reader coverage and an overwrite to a
different port. The scope is the ordered, initialized word-cell profile
with one supplied pair of Store versions.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/DeadStore/Regression.lean)

## Check the chapter 10 single-user rule

`DeadStore.SingleUser.rewrite graph version` checks the direct memory
edge for one nominated Store. Its use census reads each actual
`MemoryInput.producer` in the typed table, keeping one occurrence
for each Load, Store, or Return. The following Store must be the
only user of the nominated version. Both Stores must name the same
original typed address port. This is the initialized one-memory
profile of Simple's same-field, same-pointer, typed-pointer test:
one word-cell address identifies the entire destination.
[Pinned Simple StoreNode rule](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/SingleUser/Defs.lean)

The broader repeated deletion pass checks an interval and can pass a
disjoint reader. The single-user check refuses that reader as a second
use of the old version. Return counts as a use when it exports the
nominated heap. The table has one explicit Return and a current-version
admission rule, so this census covers its complete memory-use boundary.
The profile has no external memory consumers or parser worklist.

On success the adapter replays the existing native edit with the two
consecutive Store versions and an empty reader certificate. The later
Store takes the earlier Store's predecessor memory; subsequent edges
are renumbered while scalar wires stay in place. Cutting each graph
at the same Load ordinal and running its actual prefix proves that
every Load reads the same word. The explicit-edge return relation and
both actual typed MemRef blocks agree on the word and entire final
buffer for every typed input and initialized heap.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/SingleUser/Thms.lean)

The fixture runs both emitted blocks on a pair whose retained Store
takes its word from a prefix Load. It checks the second-use and heap
export refusals, and refuses different pointer ports even when a
sample valuation maps them to the same cell.
[Runnable fixture](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/DeadStore/SingleUser/Regression.lean)

```sh
lake build --wfail +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.SingleUser.Regression
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/DeadStore/SingleUser/Regression.lean
```

## Discover the overwrite

`DeadStore.Search.discover` takes only the original one-based version
to remove and the existing reader certificate. It verifies the
nominated Store's address and scans forward to the first Store on
that same typed wire. An observing or uncovered Load, or reaching
Return without a qualifying overwrite, stops the search. The chosen
version is strictly later and the pair passes the structural deletion
checker. `Search.rewrite` checks the listed concrete inequalities at
the invocation before rewriting.
[Search definitions](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Search/Defs.lean) ·
[Search theorems](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Search/Thms.lean)

`Memory.Loop.DeadStore.Search.rewrite` searches only the original
activation body and calls the same-activation checker. The wrapper
inherits preservation of the body result, the exit or feedback step,
exact backedge evaluation and finite returns with the whole heap.
The fixtures cover a read after the first overwrite, rejection of a
same-cell read and concrete aliasing, and a loop with only one Store
in each activation.
[Loop theorems](../../Silmaril/SSA/SeaOfNodes/Memory/Loop/DeadStore/Search/Thms.lean) ·
[Loop regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/Loop/DeadStore/Regression.lean)

## Select one dead Store

`DeadStore.Search.Selection.rewrite` takes a straight-line graph,
an ordered list of reader certificates, and the typed input tuple.
It tries original Store versions oldest first and, at each version,
tries the certificates in their supplied order. For each attempt the
nominated search chooses its first qualifying overwrite. The first
invocation-checked success returns the pair of versions, the certificate
used, and the rewritten graph. A refused attempt leaves later Store
versions available to the search. The rewrite keeps every Load and all
remaining Stores in table order. The existing deletion theorem preserves
the return and whole final heap for the checked input and any initial
heap. Selection removes one Store per call and considers only the supplied
reader certificates in this initialized straight-line profile.
[Selection definitions](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Defs.lean) ·
[Selection theorems](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Thms.lean)

The runnable fixture has two removable Stores and a certificate order
that lists the later Store's address first. Its `#eval` prints
`some (1, 2)`. An observing read blocks that pair and the search picks
`(3, 4)`. Other checks exercise concrete reader aliasing and a table
without a qualifying overwrite.
[Selection regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Thms +Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Thms +Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Search.Thms +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Forwarding.Carried.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Regression'
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Regression.lean
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Thms
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Thms
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Defs
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Correctness
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Regression
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Search.Defs
lake env leanchecker Silmaril.SSA.SeaOfNodes.Memory.Loop.DeadStore.Search.Thms
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Regression
lake env leanchecker Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.DeadStore.Regression
```

## Infer the reader certificate

`DeadStore.Search.Selection.Readers.rewrite` uses the same oldest-first
Store order and needs only the graph and its typed input tuple. For each
candidate, `Readers.discover` takes the removed Store's original address
argument and lists each Load's original address port, in table order,
strictly between that Store and the first later Store on the same wire.
It refuses a Load with no original address port or a missing overwrite.
Loads before the removed Store and after the overwrite contribute no
obligations. This uses the latest-version chain in the ordered native
graph to locate uses relevant to the initial write.
[Definitions](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Readers/Defs.lean)

The list fills `Disjoint.Certificate.writers`, which the deletion
checker uses for readers. The existing validator checks each concrete
cell disequality because distinct ports may resolve to the same cell.
The existing overwrite and reader checks decide whether to delete
the Store, and the proof identifies the returned graph with that exact
rewrite. It preserves all remaining operations in order and preserves
the returned word and entire final heap for any initial heap at the
checked input. The caller-supplied selector also remains available.
The scope is one deletion in initialized straight-line memory.
[Theorems](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Readers/Thms.lean)

The fixture reads the overwritten cell on both sides of the Store pair
and a disjoint cell between the Stores. It checks the rewritten graph
and prints `some (1, 2)`. At an aliasing input the rewrite refuses the
same inferred certificate, and the fixture shows the change in returned
word that an unchecked deletion would cause.
[Regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Readers/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.DeadStore.Regression'
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Readers/Regression.lean
```

## Repeat checked deletion

`DeadStore.Search.Selection.Readers.Repeat.rewrite` takes a graph and its
typed input tuple. It reruns the oldest-first selector after each deletion
on the newly numbered graph, discovering and checking reader obligations
at every step. It returns the final graph and the number of Stores deleted.
Simple chapter 10 registers dependencies on other uses of an earlier Store
so that its local rewrite can be retried when those uses disappear. Here,
the native ordered table is rescanned after each successful deletion.
[Pinned Simple source](https://github.com/SeaOfNodes/Simple/blob/f0a6c6757a795b8e186de0076836a87acef59fa7/chapter10/src/main/java/com/seaofnodes/simple/node/StoreNode.java#L39-L65) ·
[Pass definitions](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Readers/Repeat/Defs.lean)

Each step removes exactly one Store. The initial Store count is therefore
enough to exhaust the selector, and `rewrite_exhausted` states that the
selector returns `none` on the final graph at the checked input. This
guarantee concerns eligibility under the existing checked selector in
initialized straight-line memory. The operation projection keeps the
typed scalar operands while forgetting memory edge numbers. The order
theorem shows that only Store occurrences disappear from this list. The
return and full final heap are preserved for every initial heap at the
checked input.
[Pass theorems](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Readers/Repeat/Thms.lean)

The runnable example prints `(2, true, 1)`, giving the deletion count at
a disjoint input, the final selector's refusal, and the deletion count at
an aliasing input. The second successful step uses the renumbered Store
versions `(2, 3)`. With aliasing, the intervening Load observes the first
Store and that Store survives. The regression checks both exact output
graphs and both complete heap observations.
[Repeat regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Readers/Repeat/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Forwarding.Disjoint.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Diamond.DeadStore.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.Loop.DeadStore.Regression'
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Proofs/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Readers/Repeat/Regression.lean
```

## Run both emitted MemRef blocks

`DeadStore.Search.Selection.Readers.Repeat.MemRef.lower graph input`
returns the original and optimized typed MLIR blocks, the deletion count,
and the scalar input used to check the deletions. `runOriginal` and
`runOptimized` execute the corresponding emitted block at that scalar
input and any initialized buffer. The blocks use the existing lowering
of each ordered Load and Store to `memref.load` and `memref.store`.
[Wrapper definitions](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Readers/Repeat/MemRef/Defs.lean) ·
[Existing MemRef lowering](sea-of-nodes/memory/sea-of-nodes-memory.md#one-initialized-rank-one-memref)

`runOptimized_eq_runOriginal` compares the word and the entire final
buffer. `runOptimized_returns_iff` also identifies the optimized block's
result with the original graph's finite return relation. The proof uses
the repeated deletion theorem between the two instances of the existing
lowering theorem. The runner is total for a single initialized rank-one
`memref<nxi64>` block with typed in-bounds indices, and the observation
theorems compare results at the checked input without a fuel parameter.
[Wrapper theorems](../../Silmaril/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Readers/Repeat/MemRef/Thms.lean) ·
[Pinned upstream operations](https://github.com/llvm/llvm-project/blob/4434dabb69916856b824f68a64b029c67175e532/mlir/include/mlir/Dialect/MemRef/IR/MemRefOps.td)

The same runnable deletion fixture executes both MemRef blocks. With
disjoint addresses it deletes two Stores, and each block returns `4`
with cells `[11, 11, 1]`. With aliasing it deletes one Store, and each
block returns `8` with cells `[11, 4, 1]`.
[Executable regression](../../Silmaril/Proofs/SSA/SeaOfNodes/Memory/DeadStore/Search/Selection/Readers/Repeat/Regression.lean)

```sh
make check CHECK_TARGETS='+Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Repeat.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Search.Selection.Readers.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.MLIR.MemRef.Regression +Silmaril.Proofs.SSA.SeaOfNodes.Memory.DeadStore.Regression'
```
