# Exact rooted marking for the Prolly arena

`Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Thms` adds an executable marker
to the existing sweep checker. Initialize with the explicit local root indices;
scan the index space once in descending order. A marked resident branch adds
its local child indices. Every backward child has yet to be processed. This is
a bounded pass over the resident index space, not a linear-time cost claim:
list membership scans the marks, and shared edges may produce duplicate marks.

`mark_checked` proves that live, backward local edges reachable from the
declared roots suffice for the computed certificate to pass the unmodified
`Sweep.check`. `mark_exact` shows that every successful run marks precisely
the reachable local indices; `marked_slot` identifies retained live blocks
and precisely which in-bounds slots become holes. No index is reused,
renumbered, or compacted. Out-of-bounds indices remain distinct from holes.

External-name edges are not local indices, even if their names might also be
known elsewhere in the arena. They are not fetched during marking or sweeping,
and their later read outcomes, including missing bytes, are preserved. This is
not CAS collection and does not traverse payload links. A missing local root
or required local child fails the certificate check rather than exposing a
partially collected view.

`directoryRoots` projects a finite caller-supplied list of selected outer
keys to handles. `route_selected` preserves routed observations from those
roots. `route_directory` gives this for every entry when `CoversDirectory`
certifies that the enumeration includes all occupied keys. Any pinned readers,
pending roots, or other live handles must be supplied as roots separately;
the marker does not discover them. There is no concurrency or stale-handle
reuse claim.

Check with `lake build --wfail +Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Thms
+Silmaril.Formats.Dasl.Arena.Prolly.Sweep.Mark.Examples`.
