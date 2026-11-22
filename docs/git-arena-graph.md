# Bounded Git traversal from an arena snapshot

`Silmaril.Formats.Git.Arena.Graph` composes [arena bindings](git-arena.md)
with the [rooted Git translation](git-translation.md). A backend fixes the
source algorithm for one run. A typed OID query resolves a resident alias
or checks the supplied reader's result for an indexed placeholder. The
read-through operation is immutable: only `cache` publishes a fetched
payload, with the stronger obligation to validate all claims on that key.
No lookup of an unindexed OID implicitly invokes the reader.

The backend separates decoding, native serialization and name validation.
`GitBackend.inspect_found` gives the chosen payload, its decoder output and
the exact bytes returned by the serializer. `GitBackend.reaches_origin`
extends that provenance to every reachable local event in a successful
audited run: either the arena actually observed that payload at the name,
or a reader supplied it and the address and known kinds were validated.
It reuses the native preimage check, DAG memo, ordered parents and typed
source-to-target correspondence of the landed graph API. The native and
target naming schemes are independent.

The reader is a fixed function for the run, not a mutable remote endpoint.
The adapter recovers `.unindexed`, `.missing`, `.deferred`, `.invalid`,
`.conflict` and `.unavailable` diagnostics after the generic traversal
stops. An invalid native preimage, cycle, fuel exhaustion or unadmitted
external gitlink remains a graph fault. A shallow boundary is not a
certificate for a complete graph. The unchanged graph theorem still
requires target wire agreement for a byte audit; the adapter itself does
not choose a filesystem codec or establish target name binding.

```sh
lake build --wfail Silmaril.Formats.Git.Arena.Graph.Thms Silmaril.Formats.Git.Dasl.Layouts.Defs
lake env lean -DwarningAsError=true --run tests/formats/GitArenaGraph.lean
make check CHECK_TARGETS=+Silmaril.Formats.Git.Arena.Graph.Thms
```

The fixture traverses a root and repeated parent that share a tree and an
executable blob, completing each local address once. The parent is not
resident: the same snapshot is tested with deferred, missing, invalid and
accepted readers. It uses abstract source and target name functions; it
does not test a Git parser or a concrete hash algorithm.
