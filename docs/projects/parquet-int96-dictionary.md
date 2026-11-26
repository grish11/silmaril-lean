# Bounded dictionary INT96 chunks

`Silmaril.Formats.Parquet.Int96.Dictionary.read` reads one local column
chunk. The caller supplies the source bytes, footer boundary, expected
row count, flat leaf and column metadata, limits, and an explicit
`Policy.prolepticUtc` or `Policy.prolepticLocal`. The result is an ordered
list of nullable mathematical nanosecond coordinates on that policy's
epoch scale. The stored words and metadata do not choose the policy.
[INT96 word profile](parquet-int96.md)

The reader checks that the passed metadata describes the leaf's
singleton path, physical INT96 type and expected count, with
UNCOMPRESSED codec 0 and equal compressed and uncompressed chunk sizes.
The original `Page.readChunk` parser bounds and frames the whole extent
before interpreting pages. Limits cover total chunk bytes, declared rows,
frame count, header size, dictionary bytes and entries, and scalar and
index budgets.

- Exactly one leading dictionary is required at the declared dictionary
  offset, and at least one data page starts at the declared data offset.
  The dictionary uses PLAIN encoding 0 and exactly 12 bytes per entry.
  A later or duplicate dictionary is rejected. Identical dictionary
  values are allowed because references address positions.
- Only RLE_DICTIONARY (8) data pages are admitted. V1 and V2 may appear
  in the same chunk. PLAIN data fallback and legacy PLAIN_DICTIONARY (2)
  tags are outside this profile. The metadata may advertise PLAIN (for
  the dictionary), RLE (for levels), and RLE_DICTIONARY. A successful
  data page must still carry encoding 8 in its own header.
- Flat required fields have levels (0, 0). Optional fields have levels
  (0, 1) with width-one hybrid definition levels. V1 uses the existing
  RLE level-tag checks and optional length prefix. V2 uses the declared
  level lengths and null and row counts. Both versions consume one
  width octet and the complete checked index stream. CRC-bearing pages,
  repeated leaves, and index pages are outside this profile.

[Parquet 2.14.0 encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md) ·
[Thrift IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

Every read constructs its dictionary from its own chunk. The dictionary
is never supplied by the caller or retained for reuse by another chunk.
Errors keep the declared chunk offset. Errors after frame selection
also keep the zero-based frame ordinal (dictionary at zero) and its
absolute header offset. A bad dictionary word keeps its entry index.
A missing dictionary reference keeps both the logical slot and the
requested index, counting preceding nulls in the slot. Structural
framing errors keep the original framing cause at the chunk boundary.

## Contracts

- `readDictionary_wire` retains exact PLAIN bytes, entry count, wire order,
  and policy-selected denotation. `readDictionary_entry_error` identifies
  the first invalid word in the original entries.
- `decodeData_wire` preserves the V1/V2 body split, complete hybrid index
  stream, definition mask, and per-slot dictionary lookup.
  `decodeData_reference_error` identifies the first failed logical lookup.
- `read_wire` relates the whole result to one leading dictionary and the
  contiguous original page chain. Each ordered data frame uses that
  dictionary and the flattened slot count equals the expected row count.

[Theorem header](../../Silmaril/Formats/Parquet/Int96/Dictionary/Thms.lean)

The API stops at one chunk. Full-file dispatch, compression,
Spark rebasing, and Arrow narrowing are separate profiles.

## Independent fixtures

Pinned PyArrow 26.0.1 writes optional V1 nanosecond and V2 microsecond
files with two groups each. PyArrow independently reads each signed
group. Thrift 0.25.0 checks each leading dictionary, original offsets,
PLAIN entry bytes, and data encoding. Distinct dictionaries in adjacent
groups, repeated references, mixed nulls, negative epochs, and a
coordinate beyond signed Int64 nanos exercise the profile.

The Lean guards use the pinned files and exact byte edits. The V2
control in chunk 84 targets dictionary entry 1 and separately changes
the third present reference to index 3, which is outside the three
entries. This reference is logical slot 3 of frame 1 at header offset
134. Other controls move or duplicate the dictionary, change offsets
and encoding tags, exercise limits, and combine both data-page versions.
The scoped build runs the Lean
guards without Python dependencies.

[Fixture generator and SHA-256 pins](../../scripts/parquet-int96-dictionary/check-fixtures.py) ·
[Lean guards](../../Silmaril/Formats/Parquet/Int96/Dictionary/Tests.lean) ·
[Pinned wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Int96.Dictionary.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Int96.Dictionary.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-int96-dictionary/Axioms.lean
python3 -m venv /tmp/parquet-int96-dictionary
/tmp/parquet-int96-dictionary/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-int96-dictionary/bin/python -I scripts/parquet-int96-dictionary/check-fixtures.py
```
