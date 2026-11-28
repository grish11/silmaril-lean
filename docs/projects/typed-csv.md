# Typed nullable tables over CSV

`Silmaril.Formats.Csv.Typed` converts between the RFC 4180 wire profile and
`Silmaril.Relational.Scan.Table`. The caller supplies an ordered positional
schema of `(header field, kind)` pairs and one `CellCodec` per kind. Each codec
prints and parses the text bytes of present values. A Scan cell is an `Option`
of the value type associated with its column kind. The schema and codecs are
supplied out of band. [CSV wire profile](rfc4180-csv.md)

## Header, width and nullable text

The first record is required and must match the ordered header fields exactly.
Subsequent records must have the declared width. Header names describe positions,
so repeated names remain ordered and carry no name-based lookup semantics.

For positive-width schemas, a cell spelled `N` is null. A cell starting with
`T` holds the text bytes after that tag. `T` alone is present empty text, and
`TN` holds the text `N`. Every other tag spelling is rejected. CSV quoting works
as usual over the complete tagged field, including any embedded comma, quote or
line break. Empty or missing fields do not stand in for null. A present value
whose text conversion fails reports `printCell` or `parseCell` with the zero-based
column position. Conversions stop at the first failing row and column.

For a zero-column schema, the physical header and each physical body record are
one empty field. A table with `n` rows has `n + 1` such records, including the
header. Import checks this marker on every row and recovers the count in order.
This reserved layout lets the same lexical codec represent zero-column rows.

`importRows` and `exportRows` work on lexical rows. `decode` and `encode` add the
CSV wire decoder and canonical writer. The byte writer checks that the header and
produced cell bytes belong to the ASCII RFC 4180 profile. An empty input has no
header, and a header-only input represents an empty typed table. The adapter
requires explicit kinds and explicit codecs. Header presence inference, schema
or null inference, alternative tag conventions, and Arrow and Parquet readers
are outside this profile.

## Lean laws

- `importRows_exportRows` and `decode_encode` recover the ordered typed table
  after successful export. `CellCodec.ParsePrint` requires that parsing each
  successfully printed text recovers the original value.
- `exportRows_importRows` and `encode_of_decode` recover the exact lexical rows
  after successful import. `CellCodec.PrintParse` requires that printing each
  successfully parsed text recovers that text byte for byte. The byte theorem
  preserves the lexical observation, including each header and tagged cell.
  Field quoting and the final CRLF follow the canonical writer.
- `exportRows_zeroColumns` gives exactly one physical header plus one marker per
  typed row for width zero, independently of the cell codecs. [Public theorems](../../Silmaril/Formats/Csv/Typed/Thms.lean)

```sh
lake build --wfail +Silmaril.Formats.Csv.Typed.Thms +Silmaril.Formats.Csv.Typed.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Csv.Typed.Thms +Silmaril.Formats.Csv.Typed.Tests'
```
