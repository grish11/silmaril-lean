# Compare a selected Parquet BYTE_ARRAY leaf with Arrow BinaryView

The caller selects a Parquet leaf by exact name and required or optional
layout. `Parquet.Plain.ByteArray.File.openFile` binds it to the original
file's checked footer and `Checked.readGroup` obtains its nullable
slots from that snapshot. The source profile covers flat, uncompressed
PLAIN BYTE_ARRAY with V1 RLE levels or V2 flat levels and no page CRC.
The Arrow source is a checked IPC V5 stream with one BinaryView field and
explicit EOS. Both readers apply their own supplied bounds.
[Parquet reader profile](parquet-plain-byte-array-file.md) ·
[BinaryView observation](binary-page-observation.md)

`BinaryObservation.ParquetFile.common_observation_iff` relates the
exhausted file trace and the IPC observation. The file contributes one
batch per footer group. The common observation requires the same name,
nullability and ordered nullable octets after flattening both sources.
A null, a present empty value, an embedded zero, and non-UTF-8 bytes remain
distinct. The composition neither interprets logical annotations as text
nor emits IPC wire.

`readAll_open_error` preserves file admission errors before a schema is
available. `readAll_first_error` retains exactly the batches preceding
the first failed indexed group and copies its original typed column
error into the terminal event. The IPC side uses the existing
`observeIpc_reader_error` law for its own indexed failure.
[Theorem header](../../Silmaril/Formats/Relational/BinaryObservation/ParquetFile/Thms.lean)

## Independent fixture

The generator uses CPython 3.13.5, PyArrow 26.0.1, and Apache Thrift
0.25.0. PyArrow creates two four-row Parquet groups with `blob` at
column ordinal 1, after the required INT32 field `row_id`. Thrift
checks the original V2 page headers for PLAIN tag 0, codec 0 and no CRC
or dictionary. The independent BinaryView stream splits the eight slots
into batches of 2, 0 and 6, including inline and referenced values.
Both PyArrow and Lean verify the ordered, nullable octets.

The late Parquet control changes the length at byte 162. PyArrow still
reads group 0 and rejects group 1. Lean retains the first four slots and
reports group 1, column 1, page 0, original header offset 136, and
`integerOverflow`. Additional Lean controls cover the missing selected
field, mismatched Parquet layout, mismatched IPC field name and nullability,
and a missing IPC EOS at the boundary after record batch 2.
[Fixture hashes](../../scripts/binary-file-observation-oracle/sha256.json)

```sh
lake build --wfail +Silmaril.Formats.Relational.BinaryObservation.ParquetFile.Checks
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Formats/Relational/BinaryObservation/ParquetFile/Checks.lean
python3.13 scripts/binary-file-observation-oracle/check.py --out /tmp/binary-file-observation
```

[Parquet Format 2.14.0 encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md) ·
[Arrow 26.0.1 BinaryView and IPC](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst) ·
[Thrift 0.25.0 compact protocol source](https://github.com/apache/thrift/blob/27e8a425ffb498e190df3a12e239326bf5ba9ed6/lib/py/src/protocol/TCompactProtocol.py)
