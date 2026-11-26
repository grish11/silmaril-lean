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
