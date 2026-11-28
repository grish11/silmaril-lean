# Checked Parquet RLE BOOLEAN data pages

The Parquet Format 2.14.0 hybrid encoding spec, pinned at
`04d56f291ff963e98bc37ab8100e2fc133ff583c`, assigns raw encoding ID
`3` to RLE. Boolean values use the hybrid grammar at implicit width one.
In both Data Page V1 and V2, a four-byte unsigned little-endian length
precedes the Boolean runs. It counts only the bytes of those runs. The
same table gives different rules for other streams. V1 RLE levels have
their own length prefix, V2 levels are bounded separately, and dictionary
indices have a bit-width byte with no four-byte length. The raw upstream
`Encodings.md` SHA-256 is
`b6b980c67acc14d3e9e4b592c582523b5dc2cc09ad9f90bc2b1912df461e5c88`.
[Hybrid encoding spec][spec]

The pinned Arrow Boolean writer uses width one and writes the length in
both versions. [Arrow implementation][writer]

## Standalone callback

`Silmaril.Formats.Parquet.RleBooleanPage.decode physical params limits body`
accepts the checked column physical type, `ScalarPage.Parameters`, and the
exact on-disk page body. It requires BOOLEAN and uses
`ScalarPage.prepareFor 3` to check the raw header ID, on-disk extent and
flat layout. The accepted schemas have maximum repetition level zero and
maximum definition level zero (required) or one (optional). The caller
supplies the schema and checked parameters from its framing and metadata.

In V1, preparation decompresses the whole body and separates the level
section before deriving the present count from the mask. In V2, it
validates the uncompressed level extent and checks the mask's present
count against `num_values - num_nulls`. The bounded scalar suffix follows
the V2 value compression flag. Both versions then pass the exact
decompressed scalar suffix and the checked present count to `readValues`.
Reconstruction fills the true positions of the mask in order.

The scalar prefix must account for every remaining byte. A page with no
present values still supplies the four-byte zero length word. The
`Hybrid.Limits.bytes` byte budget excludes this word, which is included in
the page-wide bounds. The hybrid profile accepts canonical ULEB run
headers and width-one values. A repeated run must fit the remaining
count. A final packed run may have up to seven ignored padding values
with arbitrary bits. Extra bytes after the final run are rejected. These
are the inherited hybrid reader policies. Header parsing, CRC checks,
PLAIN Boolean values, nested columns and scan dispatch are outside this
callback's contract. [Hybrid reader contract][hybrid]

## Public Lean laws

- `readValues_ok_iff` characterizes the caller budgets, exact four-byte
  prefix, width-one hybrid wire relation and Boolean mapping.
- `readValues_length` gives the exact present-value count.
- `decode_ok_iff` gives the checked mask and the ordered Boolean sequence.
  Mapping `Option.isSome` recovers the mask and filtering out nulls
  recovers the values.
- `decode_wire_sound` binds BOOLEAN and raw encoding ID `3` to the
  existing exact page layout and the new exact scalar extent.
- `decode_counts` gives the total slot count and the present count from
  the checked mask, including agreement with the V2 null count.

## Independent writer fixtures

The oracle writes one uncompressed page per case with **PyArrow
26.0.1**, explicitly selecting RLE, and verifies PyArrow readback. It
uses the pinned Apache Thrift **v0.25.0** page reader to extract the
exact bytes and validate the framing fields. The six fixture rows
cover nullable mixed, required with repeated and packed runs, and
all-null cases for both versions. The oracle changes only the value
length word on each mixed page and checks that PyArrow rejects smaller,
larger and maximum unsigned lengths. The Lean examples check
the matching malformed extents, plus truncated runs, trailing bytes,
noncanonical headers, count mismatches, out-of-range repeated values,
caller limits and admitted final padding.
[Oracle][oracle] · [Fixtures][fixtures] · [Lean examples][examples]

The columns are page version, case, nullable flag, body byte length, slot
count, null count, definition payload byte length, and exact body hex.
For V1 optional pages the definition payload length excludes its own
four-byte prefix. The manifest SHA-256 is
`9865f2829d22112f81b78d721838aacd11a4985c730711102f4c4f364ffb002c`.

Use the pinned Python and Thrift artifacts. Run from the repository root.
[Flat page fixture recipe][recipe]

```sh
set -o pipefail
python3 scripts/parquet-rle-boolean-page/PyArrowOracle.py |
  diff -u tests/formats/parquet-rle-boolean-page/pyarrow-26.0.1.tsv -
lake build --wfail +Silmaril.Formats.Parquet.RleBooleanPage.Examples
make check CHECK_TARGETS=+Silmaril.Formats.Parquet.RleBooleanPage.Examples
```

[spec]: https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#rle
[writer]: https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/cpp/src/parquet/encoder.cc#L1739-L1761
[hybrid]: parquet-hybrid.md
[recipe]: parquet-flat-page.md#independent-page-fixtures
[oracle]: ../../scripts/parquet-rle-boolean-page/PyArrowOracle.py
[fixtures]: ../../tests/formats/parquet-rle-boolean-page/pyarrow-26.0.1.tsv
[examples]: ../../Silmaril/Formats/Parquet/RleBooleanPage/Examples.lean
