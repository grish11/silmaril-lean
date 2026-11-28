# Checked nullable Parquet INT96 PLAIN pages

`Silmaril.Formats.Parquet.Int96.Page.decode` reads the exact body of one
checked Data Page V1 or V2. The caller supplies the physical leaf, column
codec, original typed header, page limits, and a choice of
`Policy.prolepticUtc` or `Policy.prolepticLocal`. Both policies use uniform
86,400-second days. They give the same numerical coordinate a different
type. The page and leaf carry no evidence for choosing either policy.
[Existing INT96 word profile](parquet-int96.md) ·
[Parquet 2.14.0 PLAIN](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/Encodings.md#plain-plain--0)

The page must use PLAIN (0) and the column must use UNCOMPRESSED (0).
CRC-bearing pages receive a typed rejection. The leaf must have physical
type INT96, zero children, and required or optional repetition. The
caller establishes that the supplied leaf is flat in its containing
schema and that the page belongs to it.

- Required fields use maximum repetition and definition levels `(0, 0)`.
  There is no definition-level section. Optional fields use `(0, 1)` and
  width-one hybrid RLE/bit-packed definitions, with one slot per level and
  a 12-byte word only for a present slot.
- V1 must advertise RLE for both level encodings, including the unused
  repetition encoding. It uses the four-byte little-endian definition
  section length for optional fields. V2 uses the header's definition
  byte length and requires zero repetition bytes. Its row count must
  equal its slot count, and its null count must agree with the mask.
  Either V2 compression flag has the identity effect under codec 0.
- The shared scalar page decoder checks byte and slot budgets before
  decoding. The two header sizes must both equal the complete original
  body extent. The PLAIN suffix must consume exactly 12 bytes per
  present slot and may have neither missing nor trailing bytes.
  An invalid present word reports its zero-based logical slot index,
  counting null slots before it.

[PageHeader IDL](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/src/main/thrift/parquet.thrift)

The result keeps exact mathematical nanoseconds, including valid INT96
coordinates beyond the signed Int64 nanosecond range. Consumers can
narrow to a chosen signed 64-bit unit with the existing exact checked
conversion. This profile is a page operation. File-to-page association,
legacy Spark rebasing, dictionary encodings, compression, and timezone
resolution require separate profiles.

## Proofs

`parameters_sound` preserves the admitted leaf and all relevant fields
of the original header. `decodeSlots_eq_ok_iff` and `decode_eq_ok_iff`
recover the original nullable word sequence by re-encoding each
payload and relate the typed result to its policy-selected denotation.
`decode_wire_sound` preserves the original body extents, checked
version-specific level/suffix split, mask, and complete PLAIN suffix.
`decode_counts` preserves the advertised slot count and the V2
present count. `decodeSlots_eq_invalidWord_iff` and
`decode_eq_invalidWord_iff` identify the first invalid present word and
the complete valid logical prefix that precedes it.
[Public theorem header](../../Silmaril/Formats/Parquet/Int96/Page/Thms.lean)

## Independent fixtures

CPython 3.13.5 and PyArrow 26.0.1 write two optional INT96 files with
two row groups each. V1 uses nanoseconds and covers both signed Int64
endpoints, mixed nulls, and negative coordinates before and across the
epoch day. V2 uses microseconds and covers year 1500, mixed nulls, an
inexact millisecond conversion, and a value outside the Int64 nanosecond
range. Both files are read as signed counts at the corresponding
PyArrow unit. Independently calculated Euclidean day and subday fields
are compared with each original little-endian word.

Thrift 0.25.0 extracts the exact framed pages. A pinned byte edit changes
the second present word of the last V2 page to an invalid full-day
subday. Its logical index is 2 because a null and a valid word precede it.
The failure expectation comes from the existing INT96 subday bound.
PyArrow's signed timestamp types serve as the oracle for the valid
fixtures. Lean additionally checks both extreme signed Julian days by
their direct wire bytes, which gives wider coverage than those timestamp
types. The fixture script verifies all three file hashes and the exact
five frames embedded in the Lean tests. The library's existing module
scope selects `Silmaril.Formats.Parquet.Int96.Page.Tests` for this
change. That target builds the proof header and checks the pinned
frames without Python packages in hosted Lean CI.

[Fixture generator and pins](../../scripts/parquet-int96-page/check-fixtures.py) ·
[Scoped Lean guards](../../Silmaril/Formats/Parquet/Int96/Page/Tests.lean) ·
[Pinned Python wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Int96.Page.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Int96.Page.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-int96-page/Axioms.lean
python3 -m venv /tmp/parquet-int96-page
/tmp/parquet-int96-page/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-int96-page/bin/python -I scripts/parquet-int96-page/check-fixtures.py
```
