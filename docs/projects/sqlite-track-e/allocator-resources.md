# SQLite allocator resource contracts

The model describes the initialized public allocation family in SQLite 3.54.1,
pinned to `57520227c95396ce39ba6ecaac8d475b78dd3964`. The public API specifies
nonpositive and failed allocation, null and live free, and the ownership of
the old block after realloc. The implementation tests the request cap,
dispatches to the configured allocator, and can skip a resize when the rounded
request equals the old usable size. The default system allocator uses the
platform's size query or stores the extent alongside the allocation.
[Public API][api] · [Allocator methods][methods] · [SQLite dispatch][malloc] ·
[Default allocator][mem1]

## Observations and applicability

A pointer is null or an abstract token for an allocation lifetime. A successful
move returns a token absent from the input history and leaves a tombstone at
the old token. Freshness concerns allocation lifetimes. A native allocator can
reuse a numerical address in a later lifetime. Tokens carry no address bits.

A live block records an allocator family, owner, positive requested byte
count, and usable byte count at least as large. The calling context supplies
its allocator family, owner, and initialized profile request limit. The limit
is bounded by the release's `SQLITE_MAX_ALLOCATION_SIZE` ceiling of
2,147,483,391 bytes. The model uses family and owner as authorization facts.
Free and realloc of a non-null pointer require a live block that
matches both. A stale, unknown, foreign-family, or wrong-owner token makes the
relation inapplicable. Failure to obtain a positive request returns a null
pointer. A failed positive realloc leaves the original live block and its
ownership available. Nonpositive realloc retires a live input and returns
null. Realloc of null uses the same rule as malloc. [Release limit][limit]

The model represents initialized calls and an abstract choice among permitted
allocator replies. It does not predict whether the allocator succeeds, its
rounding rule, whether it moves storage, native addresses or alignment,
initialization effects, allocator statistics, or allocator callbacks. Signed
and unsigned API variants share the size relation after conversion to a
mathematical integer. Their ABI argument ranges and conversions are outside
the model. `Block.usable` records the extent that `sqlite3_msize` observes on
a live block. The model has no independent `sqlite3_msize` call or byte memory.
Consequently a successful realloc has no theorem that its returned block
preserves the first `min(N, M)` bytes of the old allocation, where `N` is the
new request and `M` is the old usable extent. Failure preserves metadata and
ownership. Byte contents are outside that observation as well.
[API size and copying guarantees][api] · [Realloc dispatch][realloc]

## Shared state and checked laws

Import `Silmaril.Machine.SQLite.Allocator.Thms`. `Allocator.State` is the
shared `GlobalState.AllocatorStore` with `Block` in the live allocation lane
and unit in the tombstone lane. The tombstone reserves its token without
retaining live ownership or size metadata. `Allocator.contract` writes tagged
allocation keys. `objects_preserved` gives equality of the entire object
history. `frames` gives the full lookup frame on the tagged store keys,
including object and raw allocation IDs with the same underlying value.
The lanes carry no relationship between an object's identity and the storage
used for that object. [Finite object snapshots](global-object-state.md)

| Laws | Checked observation |
| --- | --- |
| `malloc_success_lookup`, `malloc_nonpositive_iff`, `malloc_null_preserves` | A fresh live block on success and unchanged state on a null result. |
| `free_null_iff`, `free_live_iff`, `tombstone_preserved` | Null free, owned-live retirement, and the persistence of retired tokens across allocator calls. |
| `realloc_null_iff`, `realloc_nonpositive_iff_free`, `realloc_applicable_iff` | Malloc behavior for null, free behavior for nonpositive requests, and the live owner and family guard for non-null input. |
| `realloc_success_lookup`, `realloc_failure_preserves` | The new request with retained ownership, freshness and retirement on a move, and preservation of the old block on failure. |
| `lookup_preserved`, `objects_preserved`, `frames` | Untouched allocation lookups, the full object history, and the tagged observation frame. |

## Reusable resource API

Import `Silmaril.Semantics.Resource.Thms`. A `Contract` relates an input and
pre-state to a reply and post-state, with a write list for each input and reply.
`Contract.Frames` requires equality of a supplied key observation outside
that list. `Contract.seq` passes the first reply to the second input function
and concatenates the two write lists. `Contract.seq_frames` preserves their
common observation outside both. `Contract.Frames.assertion_iff` also requires
that the assertion is determined by its specified read keys and that those
keys are outside the write list.

`Allocator.Checks` composes an actual malloc with an actual moved realloc
whose input uses malloc's reply. The sequence preserves a live object whose
ID equals the retired allocation token, and preserves a separate live
allocation. Its other witnesses include realloc in place, rejection of stale,
unknown, wrong-family and wrong-owner tokens, and a failed positive resize.

## Build and replay

Use the repository's pinned Lean toolchain. From the repository root, run the
checks and replay the resource and allocator modules with the kernel replay
driver. `Allocator.Checks` also prints the public theorem axiom dependencies.
[Toolchain](../../../lean-toolchain) · [Replay driver](../../../tools/compiler-explorer/Replay.lean)

```bash
set -euo pipefail
allocator=Silmaril.Machine.SQLite.Allocator
resource=Silmaril.Semantics.Resource
lake build --wfail +"$allocator".Checks +"$resource".Thms
make check CHECK_TARGETS="+$allocator.Checks +$resource.Thms"
for module in "$resource".{Defs,Thms} Silmaril.Proofs.Semantics.Resource.Laws \
  "$allocator".{Defs,Thms,Checks} Silmaril.Proofs.Machine.SQLite.Allocator.Laws; do
  SILMARIL_REPLAY_MODULE="$module" lake env lean -DwarningAsError=true \
    tools/compiler-explorer/Replay.lean
done
```

[limit]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqliteLimit.h#L33-L47
[api]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L3260-L3339
[methods]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/sqlite.h.in#L1751-L1800
[malloc]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/malloc.c#L296-L414
[mem1]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/mem1.c#L174-L234
[realloc]: https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/malloc.c#L503-L575
