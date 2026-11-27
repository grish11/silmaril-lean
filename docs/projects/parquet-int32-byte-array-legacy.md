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

## Native mixed Arrow IPC

`Int32ByteArrayGroup.Legacy.ToIpc.convert` exhausts the checked paired
source before calling the existing mixed IPC encoder. Successful
conversion emits a V5 stream with the original selected names and
nullability in INT32-first order. The BYTE_ARRAY field is BinaryView.
`convert_readback` ties the checked readback to the original paired
events with exact octets, batch order, and EOS at the end of the
carrier. An empty footer group contributes its own empty RecordBatch.
Source refusals preserve their typed payload, and the writer runs
only after every source group succeeds.

PyArrow 26.0.1 independently decodes both selected columns and checks
the Lean-produced native stream, including `[384, 0, 384]` and exact EOS.
The opaque control replaces two bytes in a dictionary entry and two
in a long PLAIN value, preserving the original lengths and framing.
It exercises non-UTF8 and NUL octets in both BinaryView representations.
The pinned late length error returns group 2, column 1, frame 19,
header byte 21009 and yields no IPC file in the oracle.

| Artifact | SHA-256 |
| --- | --- |
| original.arrows | `be2f9535d085515eaae8e8b5a76d8222e9e3391e9b10521bff2e97d17a0db713` |
| opaque.parquet | `1500f05bd60795fdd40fa2ab3347b9bfa6b69388c731ea7be926cfc72b8fc29f` |
| opaque.arrows | `b9cae12f046e2fb4c139ac793eee4cb9855d0a5ac1151677522755bf965507ea` |

```sh
lake build --wfail +Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Checks
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-legacy-to-ipc-oracle/check.py "$fixture_tmp"
```

## Native IPC after logical scan

`Int32ByteArrayGroup.Legacy.ToIpc.Scan.convert` applies the checked legacy
event scan before exporting. The predicate sees both source cells, including
nulls, before positional projection. The existing native writers cover any
INT32-only projection, including repeated INT32 and zero fields, one
BinaryView field, and one INT32 plus one BinaryView in either order. Two
BinaryView selections can appear alone or with one INT32 in any position.
Other shapes within the IPC field limit return `.unsupportedProjection`
with the ordered projected labels. IPC budgets apply to the filtered rows,
including rows in zero-column batches.

Successful conversion certifies the IPC schema and each ordered batch
against the scan's counts and nullable cells by checked readback, with
BinaryView compared by octets. `Scan.convert_readback` ties that observation
to the original checked footer groups and the exact end of the carrier.
Each group retains one batch even when it is empty at the source or after
filtering. `Scan.convert_first_error` preserves the original indexed cause
for every predicate and projection. A late failure yields no carrier even
when the predicate would discard every row.

The PyArrow 26.0.1 comparator reuses the pinned original, opaque-byte, and
damaged files above. It independently filters the decoded Parquet groups
before comparing the native IPC fields and rows. It checks `[37, 0, 37]`
for the ordinal predicate, `[118, 0, 118]` for the nullable payload-length
predicate including a zero-column result, and `[0, 0, 0]` when all rows are
discarded. It also checks typed refusals and the original late error.

The two-view writer emits one count word per BinaryView ordinal, including
zero for a view with only inline or null values. Each column has its own
validity, views and data buffers. `TwoBinaryViews.compile_binary_wire` gives
the local slot readback and `TwoBinaryViews.record_wire` ties the packed bytes
and counts to the checked field order and descriptor ranges. The comparator
checks two selected copies of the opaque Parquet column alone and next to
INT32 in every position. A standalone stream feeds distinct short and long
Parquet values to each view and observes count vectors `[0, 1]`, `[1, 0]`
and `[0, 0]`, with the last vector belonging to an explicit empty batch.
Three view selections still receive a typed refusal.

```sh
lake build --wfail +Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Checks \
  +Silmaril.Formats.Parquet.Int32ByteArrayGroup.Legacy.ToIpc.Scan.Checks \
  +Silmaril.Formats.Arrow.MixedFlat.TwoBinaryViews.Checks
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-legacy-to-ipc-oracle/check_scan.py "$fixture_tmp"
```
