# SQLite structs in the object state store

Import `Silmaril.Machine.SQLite.GlobalState.StatePayload` to use the object
structs as the payload family of the state store.
[Object structs](object-structs.md) · [State store](global-object-state.md)

`ObjectFields Ref` accepts any reference family `Ref : ObjectKind → Type`.
Top-level object references, including references inside backend slots,
cursor fields and list links, use that family. Logical page numbers and
cache-local buffered page slots keep their scoped representations. The
indexed and flat stores use `LocalFields = ObjectFields LocalId`.

`FlatStore` is a finite dependent hash map. Its tagged key fixes its field
type, so a stored payload agrees with the key's kind by construction.
`IndexedStore.toFlat` and `FlatStore.toIndexed` preserve all lookups at
`TaggedId` keys, including absence. The two lookup laws give recovery in
both directions for these field-bearing representations.

`IndexedStore.toObjects` produces `Objects TaggedId LocalFields`. Each
object gets its kind from its tag and its fields from the corresponding
indexed map. A caller supplies `.live` or `.zombie` for each tag. This
assignment is consulted only for entries present in the struct store.
The bridge carries present snapshots. Allocation history, freshness and
lifecycle transitions stay in the state and resource layers.

`lookup_toObjects` checks exact preservation of the tag, state and typed
payload. `toObjects_toKinds` recovers the original kind erasure from this
payload-bearing snapshot. `toObjects_toStates_toKinds` specializes the
state store's `Objects.toKinds_map` law. Dropping the fields and then the
state gives the same kind map as erasing the struct store directly.
`FlatStore.lookup_toObjects` and `FlatStore.lookup_toStates_toKinds` check
the same path starting at a flat entry. The kind map retains the tagged
keys and their kinds. Field recovery uses a payload-bearing map, and
ownership and reference validity require their own premises.

The fixtures use string-named references for a statement, and a tagged
snapshot with a zombie connection and a live file at the same numeric slot.
They also check that an absent slot stays absent through conversion.

```sh
root=Silmaril.Machine.SQLite.GlobalState
lake build --wfail +"$root".StatePayloadChecks
lake env lean -DautoImplicit=false -DwarningAsError=true \
  Silmaril/Machine/SQLite/GlobalState/StatePayloadChecks.lean
for part in Flat.Defs Flat.Thms StatePayload StatePayloadChecks; do
  SILMARIL_REPLAY_MODULE="$root.$part" \
    lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean || exit 1
done
SILMARIL_REPLAY_MODULE=Silmaril.Proofs.Machine.SQLite.GlobalState.Flat.Lookup \
  lake env lean -DwarningAsError=true tools/compiler-explorer/Replay.lean
make check CHECK_TARGETS=+"$root".StatePayloadChecks
```
