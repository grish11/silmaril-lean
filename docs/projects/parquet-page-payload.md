# Checked Parquet page compression payloads

The adapter takes an exact compression slice, the declared numeric
`CompressionCodec` ID, the compressed and expected output lengths, and
separate caller caps. It accepts IDs 0 (UNCOMPRESSED), 1 (SNAPPY), 2 (GZIP)
and 7 (LZ4_RAW). Unknown IDs and the remaining known codecs, including
deprecated LZ4 (5), produce `unsupportedCodec`. The interface uses the
signed `Int` ID retained by footer metadata. The page caller validates
signed header sizes before providing natural-number sizes. [Coverage matrix](arrow-parquet-coverage.md) ·
[Parquet 2.14.0 compression][compression] · [Pinned Thrift codec IDs][idl]

The compression slice excludes page headers. For DataPageV2, separating
the uncompressed repetition and definition level prefixes, adjusting both
sizes, and applying the page compression flag belong to the page reader.
Page checksum coverage is also a separate contract.

## Exactness and budgets

The adapter checks both declared sizes against their limits and checks
the exact compressed extent before decoding. A bounded length check
inspects the declared bytes and whether a suffix exists. UNCOMPRESSED
returns that slice directly. Snappy receives the expected length as its
output cap, and LZ4_RAW receives the exact input extent, expected length
and caller caps. All successful results undergo an exact output-length
check. The preceding codec guards apply before expansion.
[Raw Snappy profile](parquet-raw-snappy.md) · [LZ4_RAW profile](parquet-lz4-raw.md)

The declared ID selects the codec relation. Byte sequences can overlap
across codec languages, so a mismatch is detected when the selected
grammar, history, or lengths fail to fit. Size and cap errors stay
distinct from malformed codecs. Snappy and GZIP report trailing input
separately. LZ4_RAW identifies extra bytes as part of a malformed raw
block via its whole-slice grammar.

GZIP admits one RFC 1952 member with DEFLATE data, a checked header and
a verified CRC-32 and ISIZE trailer. Concatenated members return
`trailingInput`. This single-member subset is narrower than Parquet's
recommendation that readers also handle multiple members.
[Parquet GZIP profile][compression-gzip] · [RFC 1952][rfc1952] · [RFC 1951][rfc1951]

The GZIP path drives the existing streaming inflater. Each call receives
the expected output size minus the bytes already emitted. In particular,
zero-capacity calls can still finish the end marker and trailer. A
pending literal or match with zero room yields `outputSizeMismatch`.
The caller also supplies `gzipCallLimit`. Each call offers a parser
scheduler budget of 64. An unfinished schedule, including a truncated
input that leaves the controller waiting, returns `gzipIncomplete`.
Successful completion requires an empty bit reservoir and no unread
input. The output invariant holds even for incomplete and rejected
runs. It bounds the logical output trace. Allocation, execution time and
completeness for a particular call budget are outside the proof.

The theorem header provides `decode_sound` for both exact lengths, both
caps, and the selected codec relation with full consumption.
`decode_rejects` gives rejection without a denotation at the expected
length, and `decode_gzip_no_exact_member` specializes it to malformed
members or a proper member with a suffix. `driveGzip_output_le` proves
the GZIP cap invariant for every schedule prefix. The remaining laws are
`Codec.ofId_id`, `decode_compressed_limit`, `decode_output_limit`, and
`decode_bad_extent`. [Theorem header][thms]

## Independent fixtures

The oracle uses PyArrow 26.0.1 from the coverage matrix and Thrift 0.25.0
to generate and extract real Parquet payloads. Each file contains one V1
data page in one row group with a required flat PLAIN INT32 column,
`[0, 1, 0, -1]` repeated 16 times. The writer options use metadata
version 2.6 and disable the dictionary, statistics and page checksums.
PyArrow reads all values back. The Thrift extractor verifies the numeric
codec in the footer and obtains the exact payload range and uncompressed
size from the page header. It compares Lean's output with a separately
packed little-endian INT32 byte sequence.
[Oracle runner][oracle] · [Apache Arrow 26.0.1][arrow] · [Apache Thrift 0.25.0][thrift]

| Numeric codec | Payload offset | Compressed bytes | Payload SHA-256 |
| --- | ---: | ---: | --- |
| 0 · UNCOMPRESSED | 26 | 256 | `3a901d720bf8b7292b7f71ae07238894cb7aded4e29c5b1cfe0e177bf4f44b79` |
| 1 · SNAPPY | 25 | 32 | `7d4bb24ed906975c555a3070cc8cf74998bc5cf0207400d01df22fc5770c5821` |
| 2 · GZIP | 25 | 33 | `b28ace7cd3b0674e46337b71b1ff445f15ee0897df140caa924df50f6c471807` |
| 7 · LZ4_RAW | 25 | 28 | `26628a5a71a02b9b8cd907c5cc170f0d8c801fb601a009d999de70521435bbe5` |

Each fixture decodes to 256 bytes with the UNCOMPRESSED digest. The
script records complete file fingerprints and checks malformed, trailing,
incorrectly declared and over-budget inputs derived from those pages.
The generators and authored controls are MIT-licensed. PyArrow and
Thrift are Apache-2.0-licensed. These fingerprints came from Linux
x86-64, CPython 3.13.5, and the following wheels.

| Wheel | SHA-256 |
| --- | --- |
| PyArrow 26.0.1 cp313 manylinux_2_28_x86_64 | `f71221bbc7707e3fad920d0478db9350791d4714ec445299ee0d56559fbc156c` |
| Thrift 0.25.0 cp313 manylinux2014_x86_64.manylinux_2_17_x86_64 | `aa0cfa1db4d2129114d9548c4fc7e85680013aa442692377606b6305d236a1c0` |

The Lean regression module embeds the extracted payloads and is included
in the existing library glob. Run the independent extractor separately.
[Regression module][tests]

```sh
lake build --wfail +Silmaril.Formats.Parquet.Payload.Thms +Silmaril.Formats.Parquet.Payload.Tests
make check CHECK_TARGETS="$(make -s scope BASE=origin/main)"
python3 -m venv /tmp/parquet-payload-oracle
/tmp/parquet-payload-oracle/bin/pip install pyarrow==26.0.1 thrift==0.25.0
/tmp/parquet-payload-oracle/bin/python -I scripts/parquet-payload-oracle/check.py
```

[compression]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md
[compression-gzip]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Compression.md#gzip
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[rfc1952]: https://www.rfc-editor.org/rfc/rfc1952
[rfc1951]: https://www.rfc-editor.org/rfc/rfc1951
[arrow]: https://github.com/apache/arrow/releases/tag/apache-arrow-26.0.1
[thrift]: https://github.com/apache/thrift/tree/27e8a425ffb498e190df3a12e239326bf5ba9ed6
[thms]: ../../Silmaril/Formats/Parquet/Payload/Thms.lean
[tests]: ../../Silmaril/Formats/Parquet/Payload/Tests.lean
[oracle]: ../../scripts/parquet-payload-oracle/check.py
