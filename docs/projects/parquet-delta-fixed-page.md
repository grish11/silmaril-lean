# Checked Parquet encoding-7 fixed-length data pages

Parquet Format 2.14.0 allows `DELTA_BYTE_ARRAY` (raw encoding ID `7`)
on `FIXED_LEN_BYTE_ARRAY`. Both length streams remain on the wire
even when the schema declares a fixed extent. The prefix lengths use
`DELTA_BINARY_PACKED`, and the suffixes use `DELTA_LENGTH_BYTE_ARRAY`.
The schema's `SchemaElement.type_length` is an `i32` byte width for the
entire column. The specification is pinned at
`04d56f291ff963e98bc37ab8100e2fc133ff583c`. The raw `Encodings.md` and
`parquet.thrift` SHA-256 digests are respectively
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`
and `d1d9a663d5543789b63d7168179d9849db06958b02c70ba96ba46ffde9278f61`.
[Encoding rules][spec] · [Schema width][schema]

## Standalone callback

Call `DeltaFixedPage.decode leaf physical params limits body` with the
matched footer leaf, the column metadata's physical type, the checked
flat page parameters, and the exact on-disk body for V1 or V2. The caller
establishes the leaf path, the flat schema levels, and the body span.
The decoder checks that both physical types agree on FIXED_LEN_BYTE_ARRAY,
the schema element has no children, and its declared width is a
positive signed-i32 value. The output is a list of nullable opaque bytes
in page order.

`ScalarPage.prepareFor 7` validates the raw header ID, level layout,
counts, and exact body extent, then establishes the checked mask and
decompressed scalar suffix. V1 derives the present count from the
mask. V2 also checks that this count equals `num_values - num_nulls` and
uses its separate value compression flag. `readValues` is available for
a caller with an exact decompressed scalar slice and known width.
[Scalar page preparation][scalar]

The scalar admission checks the width and `presentCount * width`
against the caller's per-value and total decoded-byte limits before
parsing the delta stream. It caps each encoded suffix and reconstructed
value at the declared width, retaining the tighter caller suffix cap.
The existing delta reader enforces both encoded counts, exact byte
consumption, block and padding limits, and a zero first prefix length.
A final equality check requires every reconstruction to have exactly
the declared width. An all-null page still validates its declared
width and carries both complete zero-count headers under this profile.
The caller owns scanner dispatch, logical interpretation, and framing.
[Existing delta contract][delta]

## Public Lean laws

- `selectWidth_sound` binds the positive signed width to the matched
  leaf's exact `typeLength`.
- `readValues_ok_iff` characterizes the admission caps, exact delta
  decode, and width equality for every value.
- `readValues_sound` proves exact scalar wire decomposition into the
  prefix lengths, suffix lengths and suffix bytes, with ordered
  reconstruction, exact value count, and exactly count times width
  reconstructed bytes.
- `decode_ok_iff` shows that validity recovers the checked mask and
  filtering out nulls recovers the values in order.
- `decode_wire_sound` connects the checked V1/V2 body to the schema
  width, original raw ID and the scalar wire law. `decode_counts` gives
  the total slot count and the V2 present count.

## Independent writer fixtures

PyArrow **26.0.1** at Arrow commit
`9e5d6978e9acf372cc989aaaf94e863fe8582c90` writes six uncompressed
pages using the fixed-size binary type and explicit encoding 7. Both
V1 and V2 have a width-three nullable column with opaque bytes and
repeated prefixes, a width-five required column, and a width-three
all-null column. PyArrow verifies typed readback and the footer's
physical type and width. Apache Thrift **v0.25.0** independently
extracts the header fields and exact body. Lean checks all page bytes
against the manifest and rejects wrong widths, counts, encodings,
budgets, truncation, and trailing scalar bytes.
[Writer][arrow] · [Oracle][oracle] · [Fixtures][fixtures] · [Lean examples][examples]

The manifest columns are version, case, schema width, nullable flag,
slot count, null count, definition payload size, body hex, and
decompressed scalar slice hex. For V1 optional pages the definition
payload size excludes its four-byte prefix. Manifest SHA-256 is
`4e2bcafcf6ba16e015e17d485f4b345d3fa5891f3b2ff68aa4f023909f173035`.

Use the pinned Python and Thrift artifacts from the repository fixture
recipe and run from the root. [Pinned producer environment][recipe]

```sh
set -o pipefail
python3 scripts/parquet-delta-fixed-page/PyArrowOracle.py |
  diff -u tests/formats/parquet-delta-fixed-page/pyarrow-26.0.1.tsv -
lake build --wfail +Silmaril.Formats.Parquet.DeltaFixedPage.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.DeltaFixedPage.Examples
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#deltastring
[schema]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift#L524-L533
[scalar]: parquet-scalar-page.md
[delta]: parquet-delta-byte-array.md
[arrow]: https://github.com/apache/arrow/tree/9e5d6978e9acf372cc989aaaf94e863fe8582c90
[recipe]: parquet-flat-page.md#independent-page-fixtures
[oracle]: ../../scripts/parquet-delta-fixed-page/PyArrowOracle.py
[fixtures]: ../../tests/formats/parquet-delta-fixed-page/pyarrow-26.0.1.tsv
[examples]: ../../Silmaril/Formats/Parquet/DeltaFixedPage/Examples.lean
