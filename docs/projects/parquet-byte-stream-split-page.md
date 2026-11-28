# Checked Parquet BYTE_STREAM_SPLIT data pages

`Silmaril.Formats.Parquet.ByteStreamSplitPage.Defs` composes the bounded
[scalar page preparation][scalar] and [BYTE_STREAM_SPLIT reader][split] for
one exact on-disk Data Page V1 or V2 body. Its proof header is
`Silmaril.Formats.Parquet.ByteStreamSplitPage.Thms`.

The wire rules are pinned to Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The raw `Encodings.md` SHA-256 is
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`.
[BYTE_STREAM_SPLIT wire rules][spec] · [Page headers and schema fields][idl]

## Callback and width selection

Call `decode leaf physical params limits body`. Pass the matched leaf
`Footer.SchemaElement` from the checked footer schema, its matching
`ColumnMetadata.physicalType`, and the existing `ScalarPage.Parameters` and
complete body slice from that page's frame. The caller establishes the leaf
path, flat levels, and body bounds. The decoder checks leaf arity and
physical agreement. Preparation then requires the original raw page ID
`9`, the exact on-disk extent, and a supported flat level layout.

| Footer physical type | Width source | Present slot value |
| --- | --- | --- |
| INT32 | 4 bytes | `Int32` |
| INT64 | 8 bytes | `Int64` |
| FLOAT | 4 bytes | Raw `UInt32` bits |
| DOUBLE | 8 bytes | Raw `UInt64` bits |
| FIXED_LEN_BYTE_ARRAY | `leaf.typeLength` | Opaque `Bytes` |

The fixed width is taken from `SchemaElement.type_length` on the matched
footer leaf. It must be present, positive, and below `2^31` before conversion
to `Nat`. It also has to fit the scalar width cap, including on an all-null
page. Numeric widths come from the physical type. The result carries the
selected `kind` and `slots : List (Option kind.Value)`. A typed caller can
pattern match on the kind and use the slot list at that type.

V1 uses the full-body codec and the checked flat definition section to
find the scalar suffix and present count. V2 checks the raw level extent
and header counts before decoding the value suffix under its compression
flag. Both pass the mask's present count and exact decompressed suffix to
`ByteStreamSplit.decode`. Its width, value-count, and byte budgets apply
before transposition. `FlatPage.reconstruct` places those decoded words in
the mask's true positions in order. FLOAT and DOUBLE retain every bit of
their reconstructed words, including signs and NaN payloads.

The adapter covers the five physical types above. Header parsing, frame
traversal, CRC verification, logical annotations, dictionary state, and scan
dispatch stay with the caller.

## Public proofs

- `selectKind_sound` proves physical agreement and leaf arity, and shows
  that a selected fixed width equals the declared schema width.
- `decode_ok_iff` characterizes the checked selection, exact prepared
  suffix, and reconstruction. Projecting `Option.isSome` recovers the
  original mask, and filtering absent slots recovers the typed values in
  original order.
- `decode_wire_sound` proves raw tag `9`, the selected V1/V2 wire layout,
  scalar admission, and exact lane positions for the reconstructed words.
  `decode_counts` gives the exact total slots and the V2 present count.

## Independent writer fixtures

The [manifest][vectors] records thirteen actual PyArrow **26.0.1** page
bodies from Arrow commit `9e5d6978e9acf372cc989aaaf94e863fe8582c90`.
The [oracle][oracle] uses Apache Thrift **v0.25.0** to locate the exact
bodies, decode page fields, and confirm encoding `9`. It also checks the
fixed-array schema width, every validity bit and present word on PyArrow
readback, and the original lane bytes against an independent byte-stride
calculation. Both V1 and V2 have optional INT32, INT64, FLOAT, DOUBLE, and
fixed-width BYTE_ARRAY pages, plus an all-null fixed-width page. The extra
V2 case has raw definition levels and actually Snappy-compressed INT32
lanes. The [Lean examples][lean] check all slot results and reject wrong
IDs, widths, physical types, counts, extents, and scalar width budgets.

Columns are page version, case name, physical type, fixed schema width,
compression codec ID, compressed size, uncompressed size, slot count,
null count, definition-byte count, V2 compression flag, and hexadecimal
on-disk body. A dash marks an absent width or flag. The manifest SHA-256 is
`e5357169f86b2b80c675e23a96e63fcd38444892e32a938cc6837f0caeb52c16`.

Use the pinned little-endian Linux Python and Thrift artifacts from the
[flat-page fixture recipe][flat]. With the packages on the import path,
run from the repository root.

```sh
set -o pipefail
python3 scripts/parquet-byte-stream-split-page/PyArrowOracle.py |
  diff -u tests/formats/parquet-byte-stream-split-page/pyarrow-26.0.1.tsv -
lake build --wfail +Silmaril.Formats.Parquet.ByteStreamSplitPage.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.ByteStreamSplitPage.Examples
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#byte-stream-split-byte_stream_split--9
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[scalar]: parquet-scalar-page.md#header-and-body-adapter
[split]: parquet-byte-stream-split.md
[flat]: parquet-flat-page.md#independent-page-fixtures
[vectors]: ../../tests/formats/parquet-byte-stream-split-page/pyarrow-26.0.1.tsv
[oracle]: ../../scripts/parquet-byte-stream-split-page/PyArrowOracle.py
[lean]: ../../Silmaril/Formats/Parquet/ByteStreamSplitPage/Examples.lean
