# Checked Parquet delta data pages

`Silmaril.Formats.Parquet.DeltaPage.Defs` composes the existing bounded
scalar page preparation and delta readers for one exact on-disk Data Page
V1 or V2 body. Call `decode kind params limits body` to get ordered nullable
slots. The proof header is `Silmaril.Formats.Parquet.DeltaPage.Thms`.

The wire rules are pinned to Apache Parquet Format **2.14.0**, commit
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The raw `Encodings.md` SHA-256 is
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`.
[Pinned encodings][encodings] · [Page headers and physical types][idl]

## Physical dispatch and page slices

Use `Kind.ofPhysical? column.metadata.physicalType` for the checked leaf's
physical kind, and pass the original page encoding ID in
`ScalarPage.Parameters.encoding`. The decoder checks that the ID is admitted
for the selected physical type. The indexed `Encoding kind` carries that
pairing through preparation and the scalar read.

| Physical type | Raw page tag | Scalar reader | Slot value type |
| --- | --- | --- | --- |
| INT32 | `5` DELTA_BINARY_PACKED | `DeltaBinaryPacked.decode .int32` | `Int32` |
| INT64 | `5` DELTA_BINARY_PACKED | `DeltaBinaryPacked.decode .int64` | `Int64` |
| BYTE_ARRAY | `6` DELTA_LENGTH_BYTE_ARRAY | `DeltaLengthByteArray.decode` | `Bytes` |
| BYTE_ARRAY | `7` DELTA_BYTE_ARRAY | `DeltaByteArray.decode` | `Bytes` |

The callback takes the existing [ScalarPage inputs][scalar] and full
on-disk body from the checked frame. Its `Limits.page` applies to page sizes,
levels and compression work. The other three fields supply the original
limits to the chosen scalar reader. Preparation admits flat required or
optional leaf columns with maximum repetition level zero.

- **V1** expands the full body with the column codec and checks the RLE
  definition section before passing the entire remaining scalar suffix to
  the selected reader. The present count comes from the checked mask.
- **V2** bounds and reads the raw levels, checks the present count against
  `num_values - num_nulls`, and uses the compression flag for the scalar
  suffix. The same decoder consumes that exact decompressed scalar slice.
- For both versions `FlatPage.reconstruct` places the decoded values in the
  true positions of the checked mask in order. An empty byte array is a
  present value and a null slot consumes no scalar. Encoding `7` keeps its
  previous value across null slots because only the present values enter
  the scalar reader.

The [binary-packed][packed], [delta-length][length], and [delta-byte-array][bytes]
profiles govern scalar count, padding, arithmetic and byte limits. The
adapter covers the four pairings above. Fixed-length arrays, dictionary
state and extraction, CRC, raw header parsing, scan dispatch, and logical
annotations stay outside the adapter.

## Public proofs

- `kind_ofPhysical_ok_iff` and `encoding_ofId_ok_iff` characterize physical
  and raw-ID selection exactly.
- `decode_ok_iff` characterizes the checked preparation, scalar read on
  the exact suffix at the mask's present count, and reconstruction. On
  success, mapping `Option.isSome` recovers the original mask and filtering
  absent slots recovers the scalar list in its original order.
- `decode_wire_sound` connects that same scalar slice to
  `ScalarPage.PreparedWire` for the selected V1 or V2 layout. `decode_counts`
  gives the exact total slots and the V2 header-derived present count.

## Independent writer fixtures

The [manifest][vectors] records ten actual uncompressed PyArrow **26.0.1**
Data Page bodies, Arrow commit `9e5d6978e9acf372cc989aaaf94e863fe8582c90`.
The [oracle][oracle] verifies PyArrow readback and extracts the exact body,
raw encoding and level lengths with Apache Thrift **v0.25.0**. For each
version the files cover signed INT32 and INT64 with nulls, both variable
byte-array encodings with empty and opaque bytes, and an all-null
BYTE_ARRAY page encoded with DELTA_BYTE_ARRAY. The [Lean examples][lean]
check the decoded slots, unsupported pairings and level tags, header and
mask count mismatches, malformed extents, trailing scalar bytes, and the
independent decoder budgets. The earlier scalar page suite covers compressed
bodies through the shared preparation API.

The TSV columns are version, fixture name, physical type, raw encoding
ID, slot count, null count, definition-byte count, complete body, and
scalar suffix. The final two columns contain hexadecimal bytes. Its
SHA-256 is `4e70ce2ed2b43751ec991bed02deaabe91b8881f7b752d7db062bfd73731d3ef`.

Use the pinned Python wheels and Thrift archive from the [flat-page
recipe][flat]. With the packages on the import path, run from the repo root.

```sh
set -o pipefail
python3 scripts/parquet-delta-page/PyArrowOracle.py |
  diff -u tests/formats/parquet-delta-page/pyarrow-26.0.1.tsv -
lake build --wfail +Silmaril.Formats.Parquet.DeltaPage.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.DeltaPage.Examples
```

[encodings]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md
[idl]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift
[scalar]: parquet-scalar-page.md#header-and-body-adapter
[packed]: parquet-delta-binary-packed.md
[length]: parquet-delta-length-byte-array.md
[bytes]: parquet-delta-byte-array.md
[flat]: parquet-flat-page.md#independent-page-fixtures
[vectors]: ../../tests/formats/parquet-delta-page/pyarrow-26.0.1.tsv
[oracle]: ../../scripts/parquet-delta-page/PyArrowOracle.py
[lean]: ../../Silmaril/Formats/Parquet/DeltaPage/Examples.lean
