# Checked Parquet OffsetIndex for flat INT32

`OffsetIndex.readFile limits source group column` opens a bounded plaintext
file with `Snapshot.check` and selects a zero-based row group and column.
Callers with an already checked snapshot can use
`OffsetIndex.validate limits snapshot group column`. Both index bytes and
data frames come from that snapshot. The result is `ok none` for a selected
column with both reference fields absent, or `ok (some index)` for a checked
present index. A partial pair or invalid footer interval from serialized
metadata is a typed Snapshot footer-validation error. The validator also
guards the pair directly. Malformed index bodies and mismatches against
frames have typed OffsetIndex errors.
[Snapshot API][snapshot] · [OffsetIndex API][defs]

## Profile and bounds

The profile selects a required or optional physical INT32 leaf in a flat
root schema. Other flat sibling columns can use other physical types.
The selected column's footer value count must equal the row-group count.
Dictionary chunks, a legacy `INDEX_PAGE` reference, and non-data frames
are outside this profile. Snapshot's common footer reader rejects external
columns with a nonempty `file_path` and encrypted metadata. The index
`unencoded_byte_array_data_bytes` field is for BYTE_ARRAY and is rejected
here. Other unknown Compact fields are skipped under the traversal limits.
`ColumnIndex`, Bloom filters and statistics have no role in this validation.
[Parquet page index][spec] · [ColumnChunk fields][refs] · [OffsetIndex IDL][idl]

The signed offset/length pair must designate a positive-length in-file
span between the leading magic and the footer. This profile requires the
index span to follow the selected chunk. Its byte budget is checked before a bounded byte-array extraction.
The parser applies the location cap to Compact's structural traversal as
well as the typed list read, checks all required signed fields before
converting to naturals, and requires the final STOP to consume the entire
advertised extent. List kind, field types, duplicates, and entry size are
checked. Snapshot limits bound footer traversal, and caller caps bound the
file at `readFile`, the selected chunk, row-group rows and page framing.

`Page.readChunk` supplies the actual contiguous frames. Each location matches
one frame in wire order by absolute header offset and compressed size
including the serialized header. V1 uses the header's value count for the
flat schema. V2 requires zero repetition bytes and equal value and row
counts. Each indexed page contributes a positive number of rows. The
indexed first-row values equal successive prefix sums starting at zero, and
the final sum equals the selected row-group count. Codec IDs, CRCs, levels
and value bodies have no bearing on this header-derived geometry. Success
certifies index consistency with the framed headers. Payload validity
belongs to the respective page decoders.
[Page framing API][page] · [Header counts and size][idl]

## Proof contracts

- `readExact_ok_iff` and `readPrefix_stop` bind exact index consumption to
  the Compact STOP.
- `validate_present` binds the signed footer offset and length to an exact
  checked slice, the selected column and the original page-frame sequence.
  `Evidence.pageGeometry` gives the exact header-inclusive size formula.
  `matchPages_sound` records the one-to-one ordered pairing and partition.
- `Partition.ordered` and `Partition.rowMultiplicity` give disjoint ordered
  row intervals and exactly one indexed page for each row in the group.
- `validate_absent_iff` characterizes absence by the two missing reference
  fields. `readFile_ok_iff` binds the public file entry point to the common
  checked snapshot opened from the input bytes.

[Lean theorem header][thms]

## Independent files

Pinned PyArrow **26.0.1** at Arrow commit
`9e5d6978e9acf372cc989aaaf94e863fe8582c90` wrote two groups of three data
pages each with optional INT32 values and nulls. V1 uses UNCOMPRESSED and
V2 uses Snappy. The V1 no-index control has the same rows. The oracle
independently reads back rows with PyArrow and reads the original footer,
index and frame headers with Apache Thrift **0.25.0** at
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`. The files reproduce byte for
byte. The oracle output pins SHA-256 and records each absolute offset,
header-inclusive size, and row start.
[Producer and oracle][oracle] · [Hashes and page observations][observations]

The kernel-checked Lean examples open all three files, check both groups,
and mutate the original files to trigger wrong offsets and sizes, swapped
group references, duplicate first rows, bad header counts, partial
references, truncation and surplus bytes. A changed level body serves as a
control for header-only validation.
[Lean checks][examples]

Use the pinned wheels and Thrift source archive from the flat-page fixture
recipe. From the repository root, with those packages on `PYTHONPATH`.
[Python artifact hashes][pins]

```sh
set -o pipefail
replay=$(mktemp -d)
python3 scripts/parquet-offset-index/reproduce.py "$replay" |
  diff -u scripts/parquet-offset-index/oracle.txt -
for fixture in data/parquet-offset-index/*.parquet; do
  cmp "$fixture" "$replay/${fixture##*/}"
done
lake build --wfail +Silmaril.Formats.Parquet.OffsetIndex.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.OffsetIndex.Examples
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/PageIndex.md
[refs]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L1027-L1037
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L1235-L1273
[snapshot]: ../../Silmaril/Formats/Parquet/Snapshot/Defs.lean
[page]: ../../Silmaril/Formats/Parquet/Page/Thms.lean
[defs]: ../../Silmaril/Formats/Parquet/OffsetIndex/Defs.lean
[thms]: ../../Silmaril/Formats/Parquet/OffsetIndex/Thms.lean
[examples]: ../../Silmaril/Formats/Parquet/OffsetIndex/Examples.lean
[oracle]: ../../scripts/parquet-offset-index/reproduce.py
[observations]: ../../scripts/parquet-offset-index/oracle.txt
[pins]: parquet-flat-page.md#independent-page-fixtures
