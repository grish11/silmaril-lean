# Prolly arena: closed localization

`Silmaril.Formats.Dasl.Arena.Prolly.Localize.{Defs,Thms}` consumes a fixed typed
by-name reader (for example a `Resident.capture` from the shallow or raw read
lane) and extends the dense `Indexed` arena. The caller supplies a finite
children-before-parent schedule. `checkedRoot` first uses the existing closed
scan and ordered-map check, then installs the schedule and returns a root index.
Missing, invalid wire, invalid node, fuel and inadequate schedule are failures,
not key absence. Failure exposes no staged table. A schedule may include extra
blocks; only the selected root is certified by the closed scan.

`Table.Valid` records the exact name/index inverse, occupancy coverage, successful
source reads and closure under structural block edges. Each local edge points to
an earlier index, the same liveness rule used by the indexed root directory.
A hit keeps its index;
another name for the same payload may get another slot. `Table.Extends` preserves
all previously observed lookups in both directions and all old blocks. A `Ticket`
is an index proof for a specific table and name, not a runtime generation ID; use
the extension proof to transport it. Raw `Nat` handles cannot be used as identities
across unrelated arena lineages. Keep the source snapshot pinned when reusing hits.

`Table.route_agrees` includes both results and relabelled faults, at every fuel,
from any installed root. It applies to ordinary and tagged-link keys: relabelling
does not resolve or rewrite keys or leaf payloads. `Table.lookup_sound` calls the
binding-reference theorem for the existing Prolly reader. It requires a stored
routable tree and sound captured reads relative to that reference; a different
binding extension satisfying those premises yields the same semantic answer.

This is a checked finite-schedule construction, not a verified schedule finder,
persisted generation counter, online loader, or reclamation policy. A closed scan
can read a shared block more than once; the localization table shares its index,
not necessarily the scan work. The returned arena has not published any CAS bytes.

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Dasl.Arena.Prolly.Localize.Thms +Silmaril.Formats.Dasl.Arena.Prolly.Localize.Examples'
```
