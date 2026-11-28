# Common nullable binary observations from Arrow IPC and Parquet pages

`Silmaril.Formats.Relational.BinaryObservation` exposes `observeIpc` and
`observeParquet`. Each returns the same one-column `Scan.Observation` type.
The descriptor carries the exact field name and nullability. Each row
contains an optional list of octets. Null, a present empty list, and a byte
with value zero remain distinct.

`observeIpc` uses the existing one-field little-endian V5 BinaryView reader
through its explicit end of stream. It compares the decoded name and
nullability to the requested field and accepts the binary kind. Reader
errors retain the original cause and zero-based batch index, including
an attempted EOS position. Reader errors take precedence over adapter
descriptor checks. A completed Utf8View stream receives its own rejection.
[Arrow BinaryView reader](arrow-binary-view.md)

`observeParquet` starts at caller-supplied projected page headers and exact
body windows in caller order. The caller declares the column and the
membership of those windows. The adapter checks the exact name and
nullability, physical BYTE_ARRAY, codec ID 0, and flat required or optional
levels. It accepts PLAIN V2 pages without a CRC and uses
`ScalarPage.decode (.byteArray limits)` for header counts, level decoding,
and body validation. The first failed page returns its zero-based window
index and exact cause. The result describes only the supplied windows.
Footer binding, file membership, and column-chunk completeness are outside
this API. Both adapters materialize their bounded-reader observations in
memory. [Parquet scalar page decoder](parquet-scalar-page.md)

`observeIpc_ok_iff` and `observeParquet_ok_iff` give the exact descriptor
and ordered flattening. `common_observation_iff` proves that exhausted
sources produce the same observation precisely when their descriptors and
ordered nullable octet rows agree. Page boundaries, batch boundaries,
and empty batches contribute no additional observations. `readPage_count`
ties each page's decoded size to its header count, and
`observation_rowCount` sums the component slot counts.
[Theorem header](../../Silmaril/Formats/Relational/BinaryObservation/Thms.lean)

CPython 3.13.5, PyArrow 26.0.1, and Apache Thrift 0.25.0 reproduce the
[fixture hashes](../../scripts/binary-page-observation-oracle/sha256.json).
PyArrow writes and reads two Parquet groups of four rows each and BinaryView
IPC batches of sizes `[2, 0, 6]`. Their ordered values include null, empty,
NUL, non-UTF-8 octets, and both sides of the 12-byte inline boundary.
Thrift identifies the actual projected page windows. Lean checks both
observations and eleven typed rejections, including truncated bodies,
descriptor mismatches, and multiple bad pages with the first error retained.
The oracle generates the bytes in a temporary directory.
[Fixture oracle](../../scripts/binary-page-observation-oracle/check.py)

```sh
lake build --wfail +Silmaril.Formats.Relational.BinaryObservation.Checks
lake env lean -DautoImplicit=false -DwarningAsError=true Silmaril/Formats/Relational/BinaryObservation/Checks.lean
python3.13 scripts/binary-page-observation-oracle/check.py
```

[Arrow 26.0.1 BinaryView layout](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#variable-size-binary-view-layout)
· [Parquet 2.14.0 encodings](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md)
· [Parquet DataPageHeaderV2](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L752)
