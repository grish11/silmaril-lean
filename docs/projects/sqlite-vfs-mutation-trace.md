# SQLite page hits across a bounded mutation trace

`RetainsPage page exchange` classifies successful writes on the page's
open handle whose intervals are disjoint from the page and successful
truncates on the same handle whose new lengths retain the entire page.
The classification describes one completed typed exchange.
`Trace.Valid (readWrite capacity)` checks that the bounded backing
actually produced every exchange and reached the stated final file state.
[Trace predicate](../../Silmaril/Machine/SqliteVfs/PageRead/MutationTrace/Defs.lean) ·
[Single-operation frame](sqlite-vfs-page-mutation.md)

For a complete positive-size initial page, `trace_retains_page` composes
the single-operation frame across any finite valid trace consisting of
retaining exchanges. It preserves each optional byte in the requested
interval and the mode observed through the page's handle.

`runHit_after_mutation_trace` assumes an initial live handle, admitted
page geometry, a complete initial page, and an owned vacant slot. The
original fill, mutation trace, and fresh reference fill form one valid
trace under the same bounded read-write backing. The cache hit uses the
original fill's cache and emits no VFS call. Running from the cached
bytes and running from the reference fill's bytes give the same complete
optional VDBE result at the same base, database and root, program, fuel,
and initial state. The result retains decode rejection.
[Public theorems](../../Silmaril/Machine/SqliteVfs/PageRead/MutationTrace/Thms.lean) ·
[Cache-hit contract](sqlite-vfs-cache-hit.md)

The caller supplies the initial page geometry and vacancy. The result
models a single retained page and a serial trace of the two selected
successful backing operations. Native SQLite behavior, concurrent handle
ownership, transaction effects, invalidation policy, and multi-page
coherence are outside the theorem.

```sh
lake build --wfail +Silmaril.Containers.SqliteVfs.MutationTrace.Checks
make check CHECK_TARGETS=+Silmaril.Containers.SqliteVfs.MutationTrace.Checks
```

The kernel fixtures check an adjacent write and retaining truncate between
two identical page read replies in the container runtime's typed trace.
An overlapping write fails the retaining-exchange predicate.
[Kernel fixtures](../../Silmaril/Containers/SqliteVfs/MutationTrace/Checks.lean)
