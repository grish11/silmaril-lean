# Prolly arena: publish an indexed root

`Silmaril.Formats.Dasl.Arena.Prolly.Publish.{Defs,Thms}` interprets an `Indexed`
root using the existing `RootProfile`. `stage` names local children bottom-up
and emits typed block, shallow DASL, exact bytes and the abstract partial
naming witness. Its root-name result is equal to `Indexed.name?` at every fuel,
including failure, and `eager_stage` relates that result to the eager table.
No concrete hash or new codec is needed. The profile policy does not certify
that the indexed layout is a canonical build.

`publish` sends the entire plan to `Naming.admit`. With authoritative raw
lookup (not a filtered reader), the returned raw snapshot is exactly the union
of old bytes and planned bytes. Identical repeats are admitted; conflicting
bytes, including malformed prior bytes or internal batch collisions, cannot be
replaced. With the profile's `Readback` contract every emitted block reads back
exactly; `stage_root_packed` includes the local root among those blocks.
A failed plan or collision returns neither a new root nor a partial snapshot.

External names are copied verbatim, not fetched or asserted present. This is
not a graph-completeness check, canonicality proof, memoized traversal, or
concurrent storage transaction. A backend must pin the authoritative read
snapshot until commit. The examples use fixture-only serialization and naming,
not a reusable wire profile.

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Dasl.Arena.Prolly.Publish.Thms +Silmaril.Formats.Dasl.Arena.Prolly.Publish.Examples'
```
