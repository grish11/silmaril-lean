# Sparse signed range sets

The [layout](../Silmaril/Formats/Dasl/SparseRangeSet/Defs.lean) represents a finite
set of signed 64-bit integers by maximal inclusive intervals. The intervals
are sorted and separated by at least one uncovered integer. The shallow DASL
object is one array of `[lower, upper]` arrays. The reader rejects reversed
ends, unsorted or overlapping ranges, and adjacent ranges instead of silently
normalizing them.

`normalize` inserts whole intervals and merges overlaps or adjacency; it never
enumerates every key in a range. The [theorems](../Silmaril/Formats/Dasl/SparseRangeSet/Thms.lean)
prove preservation of coverage, equality of normalized layouts exactly when
the inputs cover the same points, and equivalence with `Finset Int64`. The
finite-set interpretation may enumerate keys, but membership scans intervals
and cardinality sums widths. Arithmetic uses `Int` for endpoint comparisons
and differences and `Nat` for the total count. For example the whole signed
domain has cardinality `2^64` and fits in one 20-byte object block in both
checked profiles. No throughput or compression bound is claimed.

Wire recovery uses the [same partial profiles](atproto-dasl-sparse-int-set.md)
as the sorted integer-set layout. The shallow codec is total on normalized
layouts; byte serialization remains partial and no hash is required.

```sh
lake build --wfail +Silmaril.Formats.Dasl.SparseRangeSet.Thms +Silmaril.Formats.Dasl.Wire.Profile.Thms
lake env lean -DwarningAsError=true --run tests/formats/DaslSparseRangeSet.lean
```
