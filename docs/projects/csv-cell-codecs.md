# Concrete typed CSV cell codecs

`Silmaril.Formats.Csv.Typed.Codecs` supplies caller-selectable codecs for
signed `Int32` and `String`. These are the value types needed by the flat
Arrow interoperability profile. In typed CSV, a present cell has a `T` tag
followed by the bytes described here. Empty text produces `T` alone. A null
cell is represented by the adapter's `N` tag. [Typed CSV profile](typed-csv.md) ·
[Arrow and Parquet coverage](arrow-parquet-coverage.md)

## Signed Int32

`int32` prints every `Int32` in canonical decimal. The accepted byte spellings
are the ASCII digit `0`, a digit `1` through `9` followed by zero or more ASCII
digits, or the same positive numeral prefixed with a single ASCII minus sign.
The mathematical value must be between −2,147,483,648 and 2,147,483,647,
inclusive. The reader rejects plus signs, leading zeros, `-0`, whitespace,
non-ASCII digits, decimal points and exponents. At most 11 bytes reach numeric
evaluation. Parsing checks the mathematical range before constructing an `Int32`
and checks the spelling against its canonical rendering.

`parseInt32_eq_some_iff` relates successful parsing to the signed decimal
spelling and its denotation. `int32_parsePrint` and `int32_printParse` provide
both exact cell laws. `int32_textBytesOK` shows every rendered Int32 fits the
CSV alphabet.

## CSV-representable UTF-8

`utf8` uses the string's UTF-8 bytes directly. The supported subset is U+0020
through U+007E, plus U+000D (CR) and U+000A (LF), in any sequence including the
empty string. CSV quoting handles commas, double quotes and line breaks in the
complete tagged cell. The codec preserves the exact UTF-8 bytes, including spaces
and line breaks. Tabs, NUL, DEL, non-ASCII characters and malformed UTF-8 are
rejected. [CSV wire profile](rfc4180-csv.md) · [RFC 3629](https://www.rfc-editor.org/rfc/rfc3629)

`utf8_parse_isSome_iff` and `utf8_print_eq_some_iff` give the exact success
conditions. `utf8_parsePrint` and `utf8_printParse` give both exact cell laws on
that subset. [Public theorem header](../../Silmaril/Formats/Csv/Typed/Codecs/Thms.lean)

## Host interoperability

Use a canonical base-10 formatter and an ASCII grammar and Int32 range check
for integer text. Use strict UTF-8 conversion and the stated CSV alphabet check
for strings. The pinned CPython 3.13.5 oracle uses `str` and `int` with those
guards, and standard UTF-8 encode and decode. It checks host-produced fields in
Lean, then parses the actual Lean-produced bytes and compares the canonical
spelling. The 14 hash-pinned vectors cover both Int32 endpoints, small signed
values, empty text, tag-like text, spaces, quotes and embedded line breaks.
Lean regressions also exercise the tagged CSV representation and rejection
cases. [Fixture manifest](../../scripts/csv-codecs-oracle/fixtures.json) ·
[CPython source pin](https://github.com/python/cpython/tree/6cb20a219a860eaf687b2d968b41c480c7461909)

```sh
lake build --wfail +Silmaril.Formats.Csv.Typed.Codecs.Thms +Silmaril.Formats.Csv.Typed.Codecs.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Csv.Typed.Codecs.Thms +Silmaril.Formats.Csv.Typed.Codecs.Tests'
python3 -I scripts/csv-codecs-oracle/check.py
```
