# Arrow IPC stream to named table to CSV

`Silmaril.Formats.Arrow.ToCsv.convert` uses the checked finite IPC reader,
loads the typed table at a requested vacant database key, and exports that key
through the typed CSV writer. It takes the expected database schema and IPC
limits explicitly. The return value contains the typed schema alongside the
CSV bytes.

The reader admits the existing Arrow Columnar 1.5 / IPC V5 little-endian flat
Int32 and UTF-8 stream profile. A successful read requires explicit modern EOS
at the end of the input. Truncation, trailing bytes, unsupported IPC features,
and configured limits flow through the existing noncommitting import error.
The adapter checks row widths, value tags and required-column nulls before
offering an EOS observation to the named insertion gate.
[IPC reader contract](arrow-ipc-stream.md) ·
[Coverage matrix and standards pins](arrow-parquet-coverage.md)

The column label is the exact UTF-8 byte encoding of the Arrow field name.
The kind retains the Arrow type and nullability flag. Field position distinguishes
repeated labels. `schemaOf_injective` proves the full translation is injective.
The typed CSV record stream carries the header and tagged nullable cells.
The separately returned schema supplies kinds and nullability when reimporting.
The encoder uses the Int32 and UTF-8 cell codecs and rejects fields and text
outside the existing RFC 4180 ASCII byte profile.
[Typed CSV](typed-csv.md) · [Cell codecs](csv-cell-codecs.md)

`convert_roundTrip` assumes a successful IPC observation and typed row check,
a vacant destination, and a successful typed CSV encoding as the representability
witness. It proves conversion emits that schema and exact encoding. Decoding and
erasing the types then recovers the flattened original IPC rows in order,
including nulls, duplicates, and empty rows at schema width zero.
[Public theorems](../../Silmaril/Formats/Arrow/ToCsv/Thms.lean)

The regression fixture was produced with PyArrow 26.0.1 and read back by
PyArrow before applying CPython 3.14.7's `csv.writer` with `QUOTE_ALL` and CRLF.
It exercises the Int32 endpoints, an empty batch, null, present empty text,
a literal `N`, and text containing a comma, quotes, and CRLF. The exact octets
are embedded in the scoped Lean test closure. The manifest pins both SHA-256
digests and the producer. The generator shares the Arrow reader's pinned
wheel requirements.
[Manifest](../../scripts/arrow-to-csv-oracle/fixture.json) ·
[Fixture vectors](../../Silmaril/Formats/Arrow/ToCsv/Fixture.lean)

```sh
lake build --wfail +Silmaril.Formats.Arrow.ToCsv.Thms +Silmaril.Formats.Arrow.ToCsv.Examples
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.ToCsv.Examples'
python3 -I scripts/arrow-to-csv-oracle/fixture.py
```

To regenerate on Linux x86-64 with CPython 3.14.7, install the hashed wheel
requirements and run the generator. It checks the versions, PyArrow readback,
CPython CSV readback, and both digests before rewriting the Lean fixture.

```sh
python3 -m pip install --require-hashes -r tests/formats/arrow-ipc/requirements.txt
python3 -I scripts/arrow-to-csv-oracle/fixture.py --regenerate
```
