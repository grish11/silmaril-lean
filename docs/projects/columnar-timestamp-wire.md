# Arrow and Parquet signed timestamp value slices

`Silmaril.Formats.ColumnarTimestamp.Wire.Defs` connects the existing logical
timestamp descriptors and signed tick conversions to delimited payload bytes.
Each value is an eight-octet signed two's-complement word in little-endian
order. Both adapters reuse the verified Parquet PLAIN Int64 codec for that
physical word. The rules use Arrow 26.0.1 and Parquet Format 2.14.0.
[Arrow schema] · [Arrow columnar layout] · [Parquet encodings] · [Parquet logical types]

- `Arrow.Metadata.decodeBufferLE` and `encodeBufferLE` support seconds,
  milliseconds, microseconds and nanoseconds. The caller supplies a checked
  little-endian Arrow schema and the exact data-buffer slice without external
  padding. A nonempty timezone annotation chooses the UTC instant kind.
  Missing and empty annotations choose local wall-clock coordinates.
- `Parquet.Metadata.decodePlain` and `encodePlain` support INT64 `TIMESTAMP`
  millis, micros and nanos. The caller supplies the logical annotation from
  an INT64 leaf, and the delimited PLAIN values stream after decompression and
  level processing. `isAdjustedToUTC` chooses the UTC instant kind when true
  and the local wall-clock kind when false.

The physical count is the number of eight-byte words. Arrow validity and
Parquet definition levels are supplied by their respective layers. Short and
long slices return `.truncated` and `.trailingBytes`. Zero words require an
empty slice. The writer checks every same-kind value's conversion to the
wire unit and returns `.precisionLoss` for fractional destination ticks or
`.outOfRange` for exact results outside the signed Int64 range. It returns
bytes only on success. Both signed endpoints are representable in the
selected wire unit, and negative counts retain their sign.

`decodeLE_encodeLE` proves preservation of ordered nanosecond denotations,
including on changes of unit. `encodeLE_decodeLE` proves recovery of every
accepted byte slice and confirmation of its count. `encodeLE_isSome_iff`
characterizes success by representability of every input value. The existing
logical conversion contracts give the divisibility and range conditions.

## Integration boundary

The Arrow IPC metadata reader currently accepts Int32 and Utf8 fields. Its
future timestamp branch can supply `Arrow.Metadata` after checking the type,
unit, optional timezone and byte order. The body layer can then call this
adapter after slicing the values buffer and handling validity. The Parquet
schema and page layers can supply `Parquet.Metadata` and the count of PLAIN
INT64 values after validating the annotation and physical encoding. This
profile covers supplied descriptors and unpadded, already-delimited bytes.
Big-endian Arrow, Arrow metadata or file parsing, Parquet FlatScan, legacy
converted tags, INT96, and timezone resolution are separate profiles.

## Verification

The fixture script extracts eight IPC V5 values buffers and six uncompressed
V1 PLAIN timestamp values slices from PyArrow 26.0.1. It checks the Parquet
page header with Thrift 0.25.0 and tests each actual payload independently of
the Lean codecs. It also checks the pinned parquet-java 1.16.0 INT64 PLAIN
fixture from the [PLAIN oracle] under an explicit local timestamp descriptor.
The Java fixture supplies physical bytes only. The PyArrow cases exercise
actual timestamp metadata, all supported units and both kinds. The fixture
script checks the SHA-256 pins, including the aggregate length-framed hash
of the generated IPC streams and Parquet files. Lean regressions also check
precision loss, range overflow, negative rescaling, and malformed extents.

```sh
lake build --wfail Silmaril.Formats.ColumnarTimestamp.Wire.Thms Silmaril.Formats.ColumnarTimestamp.Wire.Tests
make check CHECK_TARGETS='+Silmaril.Formats.ColumnarTimestamp.Wire.Defs +Silmaril.Formats.ColumnarTimestamp.Wire.Thms +Silmaril.Formats.ColumnarTimestamp.Wire.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/columnar-timestamp-wire/Axioms.lean
python3 -m venv /tmp/columnar-timestamp-wire
/tmp/columnar-timestamp-wire/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/columnar-timestamp-wire/bin/python -I tests/formats/columnar-timestamp-wire/check-fixtures.py
```

The requirements pins select CPython 3.13 wheels for Linux x86-64.

[Arrow schema]: https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs
[Arrow columnar layout]: https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst
[Parquet encodings]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#plain-plain--0
[Parquet logical types]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#timestamp
[PLAIN oracle]: parquet-plain.md#independent-fixtures
