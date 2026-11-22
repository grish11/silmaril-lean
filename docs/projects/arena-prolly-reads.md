# Arena Prolly reads

The stable high-level read boundary is `Silmaril.Formats.Dasl.Arena.Prolly.Reader`
in `Silmaril.Formats.Dasl.Arena.Prolly.Defs`: a reference selects a checked or
failed typed `Silmaril.Semantics.Prolly.Block`. `Block` is the existing generic
single-layer leaf/branch type. The parameters are the reference, ordered key,
and leaf payload. The block codec is the landed DASL Prolly codec, with the
caller selecting ordinary key codecs or the tagged link-key codec. Link keys
compare by lane and name, not by resolving payloads. The structural child links
still refer to object blocks.

`readRaw` uses the selected raw-store decoder (including the object lane guard).
Use `Prolly.readBlock` for on-demand typed reads, or `Resident.capture` and
`Resident.read` to acquire a finite named snapshot in advance. Capture does not
resolve children and tests membership against an explicit acquisition list.
An unacquired name is missing in this view, not proved absent from the reference
CAS. The captured reader preserves invalid wire and invalid node separately,
and rooted queries may return a distinct fuel fault.

`Silmaril.Formats.Dasl.Arena.Prolly.Thms` proves `readRaw_sound`, exact
`Resident.read_capture` and `Resident.lookup_capture` simulations, and rooted
`Resident.lookup_sound` / `Resident.lookup_complete`. Reference membership of
fetched bytes is a premise, not inferred from parsing. Verified absence needs
the same valid rooted reference (including separator invariants) as a positive
answer. Soundness works in any binding reference containing the observations
and the represented tree, without uniqueness of names. Completeness needs enough
fuel and exact acquired blocks on the selected path, not all siblings. This is
a pure snapshot model, not a negative cache, background fetcher, or production
index; `List.lookup` currently scans the acquired table.

Filesystem consumers can define leaf payloads for typed file/directory entries
and pass a `Reader` with string keys to the existing rooted routing algorithm.
Path traversal across separate directory roots, GC, and mutation/publication are
not in this contract.
