# Date32 calendar cells in typed UTF-8 CSV

`Csv.Typed.Codecs.Date32.codec` encodes an Arrow Date32 word as a ten-byte
`YYYY-MM-DD` field. Date32 counts signed days from 1970-01-01. This profile
uses the proleptic Gregorian calendar with astronomical year zero. The first
admitted day is `0000-01-01` (−719528) and the last is `9999-12-31` (2932896).
Year `0000` and year `2000` have a February 29. Year `1900` does not.
[Arrow 26.0.1 Schema.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs)
· [Parquet 2.14.0 logical types](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#date)
· [Gregorian model and references](arrow-parquet-date.md)

The field parser consumes the entire field as ASCII digits with hyphens in
positions 5 and 8. It validates the month and day and checks exact canonical
spelling. Reduced precision, ordinal and week dates, expanded or signed
years, whitespace, clock times and offsets are outside this date-only profile.
The signed Date32 payload still supports its full range outside this codec.
[ISO 8601-1:2019](https://www.iso.org/standard/70907.html)

The `encode` and `decode` wrappers take an explicit ordered Date32 schema
and a nullability predicate over its kinds. They use the existing typed
UTF-8 CSV header, width, and CRLF wire rules. A nullable null is `N`, a
present date is `TYYYY-MM-DD`, and an empty present value fails with
`.csv (.parseCell column)`. An out-of-profile word fails with
`.csv (.printCell column)`. Required nulls report the first zero-based
row and column. Export checks required fields before framing. Import checks
required fields after successful wire, schema, and cell decoding. Export
quotes all fields as usual, and import also accepts legal unquoted fields.
The tags are the existing typed CSV convention layered over the wire grammar.
[RFC 4180 §2](https://www.rfc-editor.org/rfc/rfc4180#section-2)
· [Executable API](../../Silmaril/Formats/Csv/Typed/Codecs/Date32/Defs.lean)

`admitted_iff_signed` and `print_eq_some_iff` characterize printable words
and their unique spelling. `parse_eq_some_iff` and `parse_length` characterize
the accepted text and its width. `codec_parsePrint` and `codec_printParse` are
the standard cell laws. `decode_encode` recovers the exact ordered table,
including nulls, and `encode_of_decode` preserves the lexical rows on
re-export. The latter permits normalization of CSV quoting or the final CRLF.
[Theorem header](../../Silmaril/Formats/Csv/Typed/Codecs/Date32/Thms.lean)

## Verification

PyArrow 26.0.1 independently formats the signed Date32 words, including year
zero and the two days immediately outside the admitted profile. Its Parquet
writer produces an optional DATE column named `日付` in two row groups. The
Lean fixture uses `Parquet.Date.Events.readAll` and standard
`Arrow.Events.EventStream.collect` at EOF, keeps the field kind and nullability,
and encodes the label as UTF-8. It checks exact signed slots and compares the
export with CPython 3.13.5 `csv.writer` using `QUOTE_ALL` and CRLF. Both
`QUOTE_ALL` and `QUOTE_MINIMAL` imports recover the same slots.

CPython `datetime.date` cross-checks spellings and day offsets for years
`0001`–`9999`. That type cannot represent year zero. The year-zero dates
and the extended-year controls are checked with PyArrow's date formatting.
CPython `csv` handles those spellings as strings. The pinned negative
fixtures cover a non-leap century, trailing bytes, empty present text,
expanded and signed years, a quoted comma inside the date, null in a
required field, and an unterminated quote. Lean guards also cover signed
Int32 extrema, header/width errors and malformed UTF-8.
[Fixture hashes](../../scripts/date32-csv-oracle/fixtures.json)
· [Oracle](../../scripts/date32-csv-oracle/check.py)
· [Lean guards](../../Silmaril/Formats/Csv/Typed/Codecs/Date32/Tests.lean)

```sh
targets='+Silmaril.Formats.Csv.Typed.Codecs.Date32.Thms +Silmaril.Formats.Csv.Typed.Codecs.Date32.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
python3 -I scripts/date32-csv-oracle/check.py
```

The oracle accepts `--pyarrow-path` for a separately unpacked PyArrow wheel.
The manifest pins the Linux x86-64 CPython 3.13 wheel hash.

## Import to native Date32 IPC

`Arrow.DateStream.FromCsv.convert` takes an explicit UTF-8 field name and
nullability, a CSV byte cap and row cap, and the native IPC writer's
observation limits. It admits exactly one CSV column with the matching
logical header. The typed cell grammar and signed day limits above apply.
The output is a little-endian V5 Date32 stream with one explicitly written
batch followed by EOS. Even header-only CSV emits one zero-row batch. A
file with no header fails the existing CSV schema check.

The byte cap precedes typed CSV decoding, including header, width, cell
and required-null checks. The row cap applies to the successfully decoded
table before emission. Writer and certification failures retain the native
writer error. Every refusal returns a typed error without IPC bytes.
The converter materializes the bounded input table and emits a complete
stream. It supports one Date32 column and one batch per call.

`convert_eq_ok_iff` states the precise admission conditions and
`convert_readback` recovers the exact DAY descriptor and ordered nullable
signed words in that batch. `convert_csv_error` preserves the existing
typed decoder error after the byte cap passes.
[Executable API](../../Silmaril/Formats/Arrow/DateStream/FromCsv/Defs.lean)
· [Theorem header](../../Silmaril/Formats/Arrow/DateStream/FromCsv/Thms.lean)
· [Native DATE writer profile](arrow-date32-writer.md)

The independent readback oracle uses CPython 3.13.5 to produce CSV and
PyArrow 26.0.1 to read the actual Lean IPC output as signed Int32 Date32
storage. It checks the nullable Unicode header, a required quoted header
containing a comma, both admitted day endpoints, year zero, pre-epoch
dates, leap and century dates, and the explicit header-only batch.
CPython datetime verifies years 0001–9999. PyArrow date formatting supplies
the year-zero spelling. The pinned refusals cover the adjacent years,
invalid leap day, required null, and malformed quoting.
[Fixture hashes](../../scripts/date32-from-csv-oracle/fixtures.json)
· [Oracle](../../scripts/date32-from-csv-oracle/check.py)

```sh
targets='+Silmaril.Formats.Arrow.DateStream.FromCsv.Thms +Silmaril.Formats.Arrow.DateStream.FromCsv.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/date32-from-csv/Axioms.lean
python3 -I scripts/date32-from-csv-oracle/check.py
```

## Export from native Date32 IPC and round trips

`Arrow.DateStream.ToCsv.convert` consumes a checked one-column IPC stream
through EOS under the supplied IPC limits. The exact field name,
nullability and DAY unit must match the caller's declaration. It accepts
one explicit batch, including an empty batch, and reports the actual batch
count for schema-only or multibatch input. It checks the CSV row cap before
formatting and checks the canonical CSV byte count before returning bytes.
A present Date32 day outside −719528 through 2932896 returns the existing
typed cell print error. Nullable nulls and four-digit Gregorian spellings
use the same `N` and `TYYYY-MM-DD` grammar as the importer. The header and
cells must also be representable in the existing CSV wire profile.
[Export definitions](../../Silmaril/Formats/Arrow/DateStream/ToCsv/Defs.lean)

`readColumn_eq_ok_iff` and `convert_eq_ok_iff` characterize the admitted
IPC observation and canonical CSV output. Both round trips use the same
declared header and nullability, CSV caps, and IPC readback limits.
`csv_roundtrip` recovers the exact decoded CSV rows and succeeds when the
canonical output fits the byte cap. Quote-all framing and a final CRLF
can enlarge a valid input. `canonical_csv_roundtrip` proves byte equality
for a successful import of already canonical CSV. `ipc_roundtrip` requires
both legs to succeed and preserves the exact checked descriptor and one
ordered batch of nullable signed days. Its equality is on the checked IPC
observation. IPC metadata and padding bytes may differ.
[Theorem header](../../Silmaril/Formats/Arrow/DateStream/ToCsv/Thms.lean)

The oracle generates an optional Date32 IPC stream with both admitted
endpoints, a pre-epoch date, null, a leap day and year zero, and a required
stream with one explicit empty batch. PyArrow 26.0.1 supplies signed date
storage and the year-zero spelling. CPython 3.13.5 supplies both CSV
quoting modes and independently reads the canonical CSV output. PyArrow
reads the IPC emitted by both cycles and checks the exact schema, batch
count and signed slots. Seven PyArrow refusal fixtures cover adjacent
out-of-profile days, schema-only and multibatch input, Date64, and mismatched
name and nullability. Native guards exercise the row cap and a canonical
CSV expansion that exceeds the original byte cap.
[Fixture hashes](../../scripts/date32-ipc-csv-oracle/fixtures.json)
· [Oracle](../../scripts/date32-ipc-csv-oracle/check.py)

```sh
targets='+Silmaril.Formats.Arrow.DateStream.ToCsv.Thms +Silmaril.Formats.Arrow.DateStream.ToCsv.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/date32-ipc-csv/Axioms.lean
python3 -I scripts/date32-ipc-csv-oracle/check.py
```
