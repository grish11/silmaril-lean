# Checked legacy Parquet INT32 and BYTE_ARRAY events

`Int32ByteArrayGroup.Legacy.openSource` and `readAll` select one required
PLAIN INT32 leaf and one optional legacy BYTE_ARRAY leaf by name on the
same immutable checked snapshot. The file and row caps precede any
group read. Both selected chunks use codec 0 and Data Page V1.

The parquet-java INT32 pages have value, definition, and repetition
tags `0 / 4 / 4`. The paired reader opts into the required V1 policy.
The bound flat INT32 leaf has both level maxima zero, so its entire
page body consists of signed PLAIN words. The zero-row control uses
`0 / 3 / 4` with an empty body. The BYTE_ARRAY branch uses the existing
tag-2 dictionary and per-page tag-2 or PLAIN fallback with RLE
definitions. It accepts the retained BYTE_ARRAY binding directly.

`readGroup_wire` relates both selected original chunks to the same
footer group, proves exact ordered pairing, and recovers both slot
lists by unzipping. The event source uses the paired PLAIN source's
typed row mapping and emits one batch per complete group. Reads check
INT32 first. The first failure carries its original selected column,
group, frame ordinal, header byte and cause.

The [legacy event fixtures](parquet-byte-array-fallback.md#legacy-whole-file-events)
contain both original parquet-java 1.16.0 columns. The strengthened
Thrift 0.25.0 oracle verifies every required sibling frame. PyArrow
26.0.1 checks both columns in the original group order. Lean observes
all exact pairs and nulls in `[384, 0, 384]`. The malformed binary
fixture emits `[384, 0]` before group 2, column 1, frame 19, header
21009. Changing the final group's first INT32 value tag to 3 makes
group 2, column 0, frame 0, header 10924 the first failure with the
same complete prefix.

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-byte-array-legacy-events/Oracle.py "$fixture_tmp"
diff -r data/parquet-byte-array-legacy-events "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.Tests
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-int32-byte-array-legacy/Axioms.lean
```

## Logical scan over paired events

`Legacy.scan_readAll_order` gives one ordered output batch for each
successfully read footer group. The predicate sees both original typed
cells before projection. A false or unknown result discards that row.
The positional projection may reorder or repeat fields.
`scan_readAll_counts` counts the rows kept in each group even at zero
width. `scan_readAll_first_error` preserves the original typed failure
and the exact scanned prefix, including empty batches.

At the same projected schema, `scan_readAll_equivalent_iff` uses
`Events.EventStream.Equivalent` to compare flattened logical rows and
the typed terminal observation. The equivalence forgets batch boundaries.
The exact trace law records every batch boundary.

PyArrow 26.0.1 independently decodes both columns of the pinned legacy
files. The INT32 predicate selects 36 rows per nonempty group and
projects BYTE_ARRAY, retaining nulls when their ordinals match. The
BYTE_ARRAY length predicate keeps 118 rows per nonempty group and
projects INT32, or projects zero columns with the same counts. The
reordered, repeated projection selects BYTE_ARRAY, INT32, BYTE_ARRAY.
On the damaged file these cases preserve the first nonempty and empty
batches before the original indexed cause. A wholly unknown predicate
leaves two empty batches before the same cause.

```sh
python3 scripts/parquet-byte-array-legacy-events/ScanOracle.py \
  | diff -u tests/formats/parquet-int32-byte-array-legacy/scan-reference.txt -
lake build --wfail +Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ScanTests
```
