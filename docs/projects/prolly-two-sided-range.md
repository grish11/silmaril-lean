# Two-sided Prolly range and interval submap

`Silmaril.Formats.Dasl.Prolly.Range.Thms` exposes `scanTwoSided`, whose
successful entries are exactly the ordered slice `[lower, upper)`. Like the
original `scan`, it avoids children whose inclusive maximum is below `lower`.
At each branch it also retains only the prefix through the first maximum at
least `upper`, inclusive. That boundary child can still contain in-range
entries; in the reference tree every key in a later child is strictly greater
than the boundary separator. The proof needs both true separators and global
leaf-key ordering, not just ascending separators on the block read locally.

`scanTwoSided_stored_sound` proves agreement with any routable binding
reference that contains the observed blocks. All selected read failures still
abort the scan. In the tests a missing child skipped at an exact upper fence
is required again when that fence is widened. The old lower-pruned `scan`
keeps its prior selection and fault behavior.

`twoSided_visits_le_lower` bounds the exact selected block occurrence count by
the original lower-only count, itself bounded by a full traversal. This does
not measure unique bytes or I/O, CPU, or the cost of validating each accessed
node's entire child list. It is not an ordinal/rank algorithm.

`intervalSubmap` compares contained entries, not domain inclusion. It yields a
Boolean only after both selected scans succeed. `intervalSubmap_build_sound`
equates both Boolean answers to `OrderedMap.submap` on the semantic slices.
This comparison materializes entries and uses lookups in the second slice;
it is not an optimized merge, streaming iterator, or a proof of sharing.

Check with `lake build --wfail +Silmaril.Formats.Dasl.Prolly.Range.Thms
+Silmaril.Formats.Dasl.Prolly.Range.Examples`.
