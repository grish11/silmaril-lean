# One-group INT32 and BYTE_ARRAY projection

`Int32ByteArrayGroup.readFileRowGroup limits bytes int32 byteArray index`
opens one checked plaintext snapshot and decodes one zero-based footer
group. The two `Field` arguments give distinct exact names and required
or optional layouts. The file schema must be flat. The physical types
of the selected leaves are INT32 and BYTE_ARRAY, respectively. Other
flat siblings may have other physical types.

The result is `List (Option Int32 × Option Bytes)` in original row order.
Null and empty bytes remain distinct. INT32 values are signed physical
values, and BYTE_ARRAY values are opaque bytes. The reader supplies a
single-group entry point. [Runtime header][defs]

## Admission and error order

Both selected chunks require codec 0 and PLAIN tag 0 on every data page.
Data Page V1 with RLE level tags and V2 with flat levels are admitted.
The existing codec-0 walk rejects dictionary and non-data pages, CRC,
unsupported offsets and legacy level encodings in the selected chunks.
Footer and schema validation still covers the file, including the
metadata for unselected columns and groups. Page headers, levels and
values are checked only for the two selected chunks in the requested
group. The physical projection ignores logical annotations. Index-based
pruning and IPC conversion are separate profiles. [Shared column profile](parquet-flat-column.md)

The reader checks the file byte cap, rejects duplicate names and checks
both selections before reading either chunk. With a checked binding it
reads INT32 first, then BYTE_ARRAY, independent of physical column order.
The original cause is carried unchanged in `.int32` or `.byteArray`.
For a page failure that includes group, column, page and original header
offset. A failed read returns no pairs. A successful read checks equal
slot counts before pairing. The column caps bound the selected group and
both page walks, and the BYTE_ARRAY value cap bounds individual strings.
[Existing BYTE_ARRAY adapter](parquet-plain-byte-array-file.md)

## Proofs

- `openFile_snapshot` ties both serialized leaf lookups to the same checked
  input snapshot.
- `readGroup_of_columns` proves that two successful column reads have
  equal cardinality and produce the complete positional pairing.
- `readGroup_wire` witnesses both original indexed chunk/frame walks and
  both separate decoded slot lists. Their checked counts agree with the
  same footer group. Its pair list is their ordered zip, and unzipping
  recovers both complete lists. Page boundaries have no role in pairing.
- `readGroup_int32_error` and `readGroup_byteArray_error` state exactly
  which original error is returned at each step.

[Theorem header][thms]

## Producer verification

The four fixtures are reused byte-for-byte from
[the PLAIN BYTE_ARRAY file profile](parquet-plain-byte-array-file.md#independent-fixtures).
The format is pinned to Parquet **2.14.0**
(`04d56f291ff963e98bc37ab8100e2fc133ff583c`), with PyArrow **26.0.1**
and Thrift **v0.25.0** from the same fixture pins. Thrift independently
checks group 1's required INT32 `ordinal` page counts `[8, 4]` and
optional BYTE_ARRAY `payload` counts `[4, 8]` in both versions.
PyArrow and Lean verify the 12 ordered pairs.

The two pinned invalid files fail with `truncated` for selected
`payload` at group 1, column 1, page 1, header 608 (V1) or 646 (V2).
Selecting `ordinal` and `key` in that group succeeds while leaving
the damaged `payload` unselected. A separate Lean control changes the
V2 INT32 page tag in the already damaged file. Both independent column
calls fail, and the paired call returns the original INT32
`.encoding 3` at group 1, column 0, page 1, header 513.
[Lean regressions][tests] · [Independent projection oracle][oracle]

```sh
fixture_tmp=$(mktemp -d)
python3 scripts/parquet-plain-byte-array-file/Oracle.py "$fixture_tmp"
diff -r data/parquet-plain-byte-array-file "$fixture_tmp"
python3 scripts/parquet-int32-byte-array-group/Check.py "$fixture_tmp"
lake build --wfail +Silmaril.Formats.Parquet.Int32ByteArrayGroup.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Int32ByteArrayGroup.Tests +Silmaril.Formats.Parquet.Plain.ByteArray.File.Tests +Silmaril.Formats.Parquet.MixedBooleanFloat.Tests parquet-flat-scan-regression parquet-page-regression'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/parquet-int32-byte-array-group/Axioms.lean
```

[defs]: ../../Silmaril/Formats/Parquet/Int32ByteArrayGroup/Defs.lean
[thms]: ../../Silmaril/Formats/Parquet/Int32ByteArrayGroup/Thms.lean
[tests]: ../../Silmaril/Formats/Parquet/Int32ByteArrayGroup/Tests.lean
[oracle]: ../../scripts/parquet-int32-byte-array-group/Check.py
