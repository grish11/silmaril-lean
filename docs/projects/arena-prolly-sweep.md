# Prolly arena: checked reachability sweep

`Silmaril.Formats.Dasl.Arena.Prolly.Sweep.{Defs,Thms}` checks a finite list of
marked indices against a dense `Indexed` snapshot and **all declared roots**.
Every marked index must be occupied and every local structural child of a
marked block must be marked. External edges are preserved unchanged; external
reads cannot manufacture local handles. Names embedded in keys and values
remain untouched. The sweep does not reclaim any external CAS data.

The result retains the index address space with optional entries: an in-bounds
hole denotes a reclaimed slot; an out-of-bounds index is distinct. Neither
becomes a negative key answer. There is no slot reuse, compaction, or cross-lineage
handle guarantee. A caller may supply an over-approximation (for example to
retain an old handle); the checker does not compute least reachability.

`route_reachable` proves exact equality for any routed query from a reachable
handle, including external read, invalid-node, and fuel faults. It does not
assume external completeness or silently guess an unresolved child's data.
An incomplete mark list, stale root or non-existent mark fails before any
new view is returned. The proof does not cover concurrent mutation, external
persistence, or replacing a root by a newly edited tree.

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Thms +Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Examples'
```
