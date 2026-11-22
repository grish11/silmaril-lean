# Prolly arena: copy on write at a root handle

`Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot.{Defs,Thms}` separates a generic
outer root key from its current internal handle. `Directory.copy?` appends one
caller-proposed root block and switches only the chosen directory entry (which
may be new). It rejects non-live local children before returning an updated
directory. An external child remains external, without assuming availability.

`copy_spec` gives the exact directory and block frame and preserves directory
liveness with backward local edges. `route_old` preserves routed results and
faults for each old live handle, including aliases of the replaced root. The
new root is fresh in this lineage; it is not a globally valid identifier and
the operation does not update any prior CAS name.

This is the root-handle transition, not a path edit, validation of a proposed
tree, runtime linear capability or persisted transaction. The next edit proof
must supply new rooted correctness and compare local rebuilding with the shared
map semantics. A caller of the sweep API must explicitly declare every root
it wants retained, including old-root aliases and separately pinned handles.

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot.Thms +Silmaril.Formats.Dasl.Arena.Prolly.CopyRoot.Examples'
```
