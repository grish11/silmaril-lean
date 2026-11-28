# Dictionary-coded Parquet TIMESTAMP to native Arrow IPC

`Timestamp.Leaf.Dictionary.convert` binds one flat required or optional
INT64 TIMESTAMP leaf in a checked snapshot and emits its footer groups as
Arrow V5 record batches. The leaf ordinal includes the schema root at
zero. The explicit annotation profile accepts either modern TIMESTAMP or,
with `.allowConvertedOnly`, legacy converted-only millis or micros. Its
interpretation, unit and signed counts carry through unchanged. The output
uses `UTC` for adjusted instants and an absent timezone for local readings.

The dictionary path admits only uncompressed chunks. Each group requires a
single leading PLAIN dictionary page at the advertised dictionary offset,
followed by one or more V1/V2 data pages encoded RLE_DICTIONARY. The first
data header starts at the advertised data offset. PLAIN fallback data,
legacy PLAIN_DICTIONARY encoding, CRC-bearing frames, index pages and
compressed dictionary chunks are refused. The regular TIMESTAMP converter
keeps its PLAIN profile and existing Snappy opt-in.

[Selected TIMESTAMP leaf](parquet-timestamp-leaf.md) ·
[Converted-only annotations](parquet-converted-timestamp.md) ·
[Parquet encoding specification](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#dictionary-encoding-plain_dictionary--2-and-rle_dictionary--8)

## Bounds and provenance

The shared chunk selector checks the selected group, leaf and chunk
ordinals against the retained snapshot, including singleton path,
physical type, row count and disjoint byte span. The dictionary reader
bounds the chunk before framing. It checks the total declared data slots
before decoding the dictionary or any data page. Dictionary entry and byte
limits apply before reading the PLAIN body. The existing scalar page and
index checks bound page extents, level masks and the width-prefixed Hybrid
index stream. Each group resolves references against its own dictionary.

`checkGroup_wire` exposes the exact parent chunk and the original contiguous
frames. `readEntries_wire` ties each dictionary entry to an original signed
PLAIN word. `data_decodes` identifies the exact level and index slices and
the nullable slots they reconstruct. `readGroup_wire` relates their
concatenation to the group observation with the original annotation.
The event and IPC laws preserve the footer-order groups. A late page failure
retains its group index, wire page ordinal, absolute header offset and cause.
Page zero is the dictionary. Events retain earlier complete groups, and
conversion returns the source failure before attempting IPC emission.

[Dictionary laws](../../Silmaril/Formats/Parquet/Timestamp/Leaf/Dictionary/Thms.lean) ·
[Shared dictionary index laws](../../Silmaril/Formats/Parquet/DictionaryIndex/Thms.lean)

## Pinned interoperability

CPython 3.13.5, PyArrow 26.0.1 and Thrift 0.25.0 reproduce six input files.
PyArrow writes modern UTC nanos V1 and modern local micros V2. A deterministic
Thrift footer edit over PyArrow UTC micros V2 pages supplies the
converted-only case. All three successes select a nullable leaf beside an
INT32 decoy. Each file has three distinct chunk-local dictionaries, repeated
values, nulls and both signed Int64 endpoints. Thrift verifies the dictionary
entries, page versions, level bytes, actual index streams and offsets.
PyArrow checks the actual native Arrow IPC field and all three batches.

The pinned refusal cases include an out-of-range packed reference in the
last group, a genuine PyArrow writer fallback to PLAIN, and a Snappy
dictionary chunk. The late reference control checks the exact two-batch
prefix and original typed source failure. Additional controls cover default
policy, selection, and independent chunk, page, entry, dictionary body and
index limits.

[Oracle](../../scripts/parquet-timestamp-dictionary-oracle/check.py) ·
[Fixture hashes](../../scripts/parquet-timestamp-dictionary-oracle/fixtures.json) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Timestamp.Leaf.Dictionary.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-timestamp-dictionary-oracle/Axioms.lean
python3 -m venv /tmp/parquet-timestamp-dictionary
/tmp/parquet-timestamp-dictionary/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-timestamp-dictionary/bin/python -I scripts/parquet-timestamp-dictionary-oracle/check.py
```
