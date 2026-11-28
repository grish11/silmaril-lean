# RFC 4180 CSV wire profile

`Silmaril.Formats.Csv.Defs` reads and writes whole CSV files as ordered lists
of rows. Each row contains one or more fields, and each field contains its
unescaped bytes in order. The byte grammar `Parses` is available through the
`ByteFormat` interface. The profile uses RFC 4180 §2. [RFC 4180, October 2005](https://www.rfc-editor.org/rfc/rfc4180#section-2)

## Admitted bytes and record choices

- Bare fields use RFC 4180 `TEXTDATA`, `%x20-21 / %x23-2B / %x2D-7E`.
  Quoted fields additionally allow commas, CR and LF, and represent each
  literal quote by a doubled quote. CR and LF are preserved byte for byte
  inside quotes, including a CRLF pair.
- Comma separates fields. Spaces are field data, including leading and
  trailing spaces in bare fields. A closing quote must be followed by comma,
  CRLF or end of input. CRLF separates rows, and the final row may omit its
  terminator. Bare CR and LF, tabs, other control bytes, non-ASCII bytes and
  a UTF-8 BOM are rejected outside the admitted productions.
- The zero-byte file denotes zero rows. A bare CRLF is one row with one empty
  field, and `""` is another spelling of one empty field. A final CRLF
  terminates the last row. An additional CRLF represents an additional empty
  record. These choices resolve the nullable record in the RFC grammar.
- The parser reports exactly the fields on each row. For `a,b,` the final
  comma introduces an explicit empty third field under the ABNF. A row
  containing `a,b` has two fields, even alongside three-field rows. Ragged
  rows are admitted at this lexical layer, without padding. The first row has
  the same representation as later rows. Empty cells and literals such as
  `NULL` remain byte fields. Header metadata, equal-width policy, null
  inference, typed cell conversion and further CSV dialects are outside the
  profile.

The writer quotes every field, doubles quotes, and emits CRLF after every row.
It emits zero bytes for zero rows, and it rejects zero-field rows or field bytes
outside the admitted alphabet. The codec works in memory on byte lists and
reports failure as `none`. The file framing, spelling of fields and original
presence of the final CRLF can vary between spellings of the same rows.

## Lean laws

- `decode_eq_some_iff` characterizes successful decoding by the independent
  whole-input grammar, in both directions.
- `parses_wellFormed` gives nonempty rows and representable field bytes for
  every grammatical file.
- `encode_eq_none_iff` characterizes writer rejection by `WellFormed`.
- `encode_sound` proves that every emitted file is grammatical for its input
  rows. `decode_encode` recovers those rows, including their arities and every
  field byte. [Public theorem header](../../Silmaril/Formats/Csv/Thms.lean)

## Fixtures and checks

The fixture manifest pins ASCII wire bytes and canonical writer SHA-256s.
It includes fixtures produced by CPython 3.13.5 `csv.writer` and hand-written
reader inputs with expected ordered rows. The harness compares the actual Lean
writer bytes with CPython's output and checks both readers against the pinned
rows. Its settings use comma, double quote, doubled internal quotes and no
space skipping. The writer uses `QUOTE_ALL` and CRLF. The oracle checks only
shared behavior on these fixtures. For example, the Lean regressions separately
check the profile's interpretation of a bare CRLF as a single empty field and
its rejection of a bare LF separator. The fixture data is original to this
repository. [Fixture manifest](../../tests/formats/csv/fixtures.json) · [Pinned CPython `_csv` source](https://github.com/python/cpython/blob/6cb20a219a860eaf687b2d968b41c480c7461909/Modules/_csv.c)

Run from the repository root with the pinned Lean toolchain and CPython 3.13.5.
The Lean regression module is included in the existing Formats library glob.
The independent fixture comparison runs as a separate command.

```sh
lake build --wfail +Silmaril.Formats.Csv.Thms +Silmaril.Formats.Csv.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Csv.Thms +Silmaril.Formats.Csv.Tests'
python3 -I tests/formats/csv/check_fixtures.py
```
