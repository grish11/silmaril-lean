# Bounded PLAIN Parquet scalar pages

`Silmaril.Formats.Parquet.ScalarPage.Defs` composes the bounded [payload
reader][payload], [flat definition levels][flat], and [PLAIN decoder][plain].
Call `ScalarPage.decode kind params limits body` with the exact on-disk body
and the checked header and column fields. It returns ordered `Option` slots
of the selected physical type. `prepare` exposes the checked definition mask
and decompressed scalar suffix for clients that need those slices directly.
The theorem header is `Silmaril.Formats.Parquet.ScalarPage.Thms`.

The wire specification is Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The raw `parquet.thrift` SHA-256 is
`d1d9a663d5543789b63d7168179d9849db06958b02c70ba96ba46ffde9278f61`.
[Data pages][pages] · [PageHeader IDL][idl] · [Encodings][encodings]

## Header and body adapter

Use the bytes in the half-open payload span immediately after `PageHeader`.
With `Parquet.Page.Frame`, this is `frame.payload` in the source that yielded
the frame. The adapter takes these fields explicitly so it can be used with
any header reader.

| Input | Source |
| --- | --- |
| `Parameters.sizes` | `Header.compressedSize` and `Header.uncompressedSize`, in that order |
| `Parameters.numValues`, `Parameters.encoding` | `DataV1` or `DataV2` fields of the same names |
| `Parameters.version` for V1 | `.v1 header.definitionLevelEncoding header.repetitionLevelEncoding` |
| `Parameters.version` for V2 | `.v2 header.numNulls header.numRows header.repetitionBytes header.definitionBytes (some header.isCompressed)` for the projected Boolean. A reader retaining the optional wire field can pass it directly. |
| `Parameters.schema`, `Kind` | Maximum levels and physical type from the selected leaf schema. Fixed length byte arrays also need a positive schema width. |
| `Parameters.codec` | Column chunk compression codec ID |
| `Limits` | Caller caps for both full page sizes, the number of slots, definition bytes, and GZIP controller calls |

The Thrift sizes, counts, and level byte lengths are signed `i32` fields on
the wire. Reject negatives before converting them to `Nat`. `decode` checks
page size and slot bounds, the schema profile, the PLAIN ID, and exact input
length before expanding a payload. A successful V1 or V2 decode accounts for
every level byte and scalar byte, subject to the padding policies below.

- **V1.** The column codec applies to the whole body. A required page has
  no level bytes. An optional page has a four-byte little-endian definition
  length, then exactly that many Hybrid bytes, then the PLAIN values. The
  number of present scalars is the count of true entries in the checked
  mask. V1 supplies only the slot count.
- **V2.** The levels precede the value section and are stored uncompressed.
  Flat pages require zero repetition bytes and `num_rows = num_values`.
  The definition length must fit both declared page sizes and its own byte
  cap before subtracting it from either size. The bounded raw definition
  prefix uses Hybrid without a V1 length word. The decoded mask must
  contain `num_values - num_nulls` present slots after checking
  `num_nulls ≤ num_values`. `is_compressed = false` uses the scalar suffix
  verbatim even if the column codec is Snappy. An absent flag defaults to
  `true`, which uses the declared column codec for that suffix only.

The checked profile accepts maximum repetition level zero and maximum
definition level zero or one. V1 requires both level encoding IDs to be RLE
(`3`), including when a level stream is omitted. V2 uses its implicit RLE
level format. PLAIN (`0`) covers signed INT32 and INT64, LSB-first Boolean,
raw 32/64-bit float words, fixed length byte arrays, and
[length-prefixed byte arrays](parquet-plain-byte-array.md). The latter use
`Kind.byteArray` with separate scalar-slice and per-value byte caps. The float results
preserve every bit, including NaN payloads and signed zero. Unused high bits
in the final PLAIN Boolean byte are ignored. Hybrid ignores the bits of at
most seven surplus values in the final bit-packed run and rejects extra
level bytes.
Selected compression follows the existing payload codec profile, which
supports UNCOMPRESSED, SNAPPY, bounded single-member GZIP, and LZ4_RAW.

Thrift header parsing, span discovery, CRC verification, dictionary pages and
encodings, INT96, repeated or nested columns, logical types,
and table reconstruction are outside this adapter.

## Public proofs

- `splitV2_ok_iff` characterizes exactly the two guards on the definition
  length, the bounded prefix, and the byte-for-byte concatenation of the
  prefix and encoded scalar suffix.
- `prepare_sound` gives exact encoded and decoded byte sizes and the
  selected codec relation for V1’s complete body or V2’s scalar suffix.
  It also identifies the exact level slice used by the checked mask.
  `prepared_v1_slices` gives the complete decompressed V1 decomposition,
  including the optional four-byte length word. `prepared_mask_length`
  proves that both layouts have one mask entry per declared slot.
- `readPlain_size` proves the exact PLAIN scalar byte count. `decode_sound`
  proves that projecting `isSome` gives the original mask and filtering out
  absent values gives exactly the PLAIN list in wire order. `decode_counts`
  proves the slot count and, for V2, the header-derived present count.

## Independent writer fixtures

The [TSV][vectors] contains INT32 PLAIN bodies and selected header fields
from seven one-page files written by PyArrow **26.0.1**. The Arrow release commit is
`9e5d6978e9acf372cc989aaaf94e863fe8582c90`. The [oracle][oracle] checks read-back,
leaf levels, physical encodings, and single-page extents. It extracts header
fields via Apache Thrift **v0.25.0**, commit
`27e8a425ffb498e190df3a12e239326bf5ba9ed6`. The tests cover mixed and all-null
pages, raw and whole-body Snappy V1, V2 with `is_compressed = false` despite a
Snappy column codec, and V2 with raw levels and a compressed scalar suffix.
The V2 compressed fixture repeats `[7, null, -4, null, 19]` sixteen times.

The columns are page version, compression, case name, numeric codec,
compressed size, uncompressed size, number of slots, V2 null count, V2 row
count, V2 repetition bytes, V2 definition bytes, V2 compression flag, and
hexadecimal on-disk body. A dash marks an absent field. The SHA-256 is
`6a81e13807872a973f4b17ca538c4157c98b5237223ae2525383808888cf64b1`.
The [Lean examples][examples] bind these rows to executable checks and add
malformed extent, count, encoding, trailing-byte, and resource-limit cases.

Use the pinned CPython 3.13 Linux x86-64 PyArrow and NumPy wheels and Apache
Thrift source archive listed in the [flat-page fixture recipe][flat]. With
those artifacts on `PYTHONPATH`, run the following from the repository root.

```sh
set -o pipefail
python3 scripts/parquet-scalar-page/PyArrowOracle.py |
  diff -u tests/formats/parquet-scalar-page/pyarrow-26.0.1.tsv -
lake build --wfail +Silmaril.Formats.Parquet.ScalarPage.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ScalarPage.Examples
```

[pages]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/README.md#data-pages
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[encodings]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md
[payload]: parquet-page-payload.md
[flat]: parquet-flat-page.md
[plain]: parquet-plain.md
[vectors]: ../../tests/formats/parquet-scalar-page/pyarrow-26.0.1.tsv
[oracle]: ../../scripts/parquet-scalar-page/PyArrowOracle.py
[examples]: ../../Silmaril/Formats/Parquet/ScalarPage/Examples.lean
