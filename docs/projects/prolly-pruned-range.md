# Prolly: a checked separator-pruned range scan

`Silmaril.Formats.Dasl.Prolly.Range.{Defs,Thms}` gives an ascending half-open
`[lower, upper)` scan. It skips a subtree when its inclusive maximum is strictly
below `lower`. The upper endpoint filters leaf entries, but does not yet prune
the right-hand subtrees. A reversed or empty interval therefore still checks
the selected nodes and can return a read fault. The reader is the existing
typed block interface, so ordinary and name-keyed trees share the algorithm.

`scan_stored_sound` gives exact entries against every binding reference
containing a stored routable tree and the successful read observations. Truthful
subtree maxima and global ordering come from that reference, not the local
shape test. A missing or invalid selected block or inadequate fuel aborts;
omitted blocks may be unreadable when their *verified* intervals exclude the
requested keys. A successful scan with no such reference does not certify
absence. `scan_build_sound` relates the returned entries to the extensional
`mapSlice` of the existing `OrderedMap` underlying a canonical `build`.

On success, `visits` is exactly the number of selected block occurrences (one
per typed read in the scan, even if names repeat), which `visits_le_all` bounds
by a full traversal. The count excludes failed traversals, cache misses, byte
traffic, comparisons and output allocations. The examples show a four-read full
scan and a three-read range scan where a skipped child is missing. This is not
a two-sided seek, subtree-statistics proof, rank operation, or new-root build.

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Dasl.Prolly.Range.Thms +Silmaril.Formats.Dasl.Prolly.Range.Examples'
```
