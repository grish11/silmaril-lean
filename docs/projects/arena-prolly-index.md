# Append-only Prolly index experiment

`Silmaril.Formats.Dasl.Arena.Prolly.Index.{Defs,Thms}` keeps the named read
interface and reuses its single-layer `Block`. A `Handle Name` is either a local
array index or an external CAS name. `Indexed.acquire` reads a typed block from
the named reader, localizes only explicitly selected edges, and allocates the
block. It propagates read errors; `ok none` indicates a rejected forward edge,
not key absence. An unlocalized edge remains an external name even if its
numeric representation coincides with a local index. No hashing is needed to
allocate, localize, or run a query.

`Indexed.append_spec` proves fresh allocation at the old length and stable
old reads. `Indexed.append_local_live` proves every admitted local edge of a
new branch pointed to an existing block and still points to it after the
append. Thus appending in this lineage cannot rebind a live edge or root.
There is no delete, compaction, in-place edit, or cross-arena handle check.
Clients must use the same append lineage and must not forge handles.

`Indexed.acquire_spec` identifies the exact source block installed under a new
index. `localize_relabel` states when localization preserves the original block.
`route_refines` projects successful answers (including `ok none`) through a
successful-read simulation. `Indexed.lookup_sound` composes this with the
named snapshot theorem, and requires the explicit projection/reader agreement
and a valid rooted representation in a binding reference. Local index
liveness alone cannot prove that a localization maps to the correct name,
nor that runtime separator tests justify a semantic negative. The experiment
does not construct a whole verified name-to-index table or prove the converse
simulation for an arbitrary partially localized snapshot.

`Indexed.name?` chooses local names bottom-up on demand; already external names
pass through unchanged. `Indexed.eagerNames` fills an array up front and
`eagerNames_at` proves exact agreement at the same fuel and choice function.
The eager reference implementation repeats work across roots. Neither mode
checks integrity of external names, establishes binding of newly named blocks,
or publishes them. Next: a sharing-aware bottom-up pass, conditional coherent
localization/binding and collision-safe publication, then reachability GC and
an explicit stable-handle policy for reclamation.
