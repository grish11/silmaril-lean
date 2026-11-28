# Selected dictionary INT96 in a Parquet file

`Silmaril.Formats.Parquet.Int96.Dictionary.File.openFile` checks a bounded
immutable Parquet source and binds one named flat required or optional INT96
leaf. The caller supplies `Policy.prolepticUtc` or `Policy.prolepticLocal`.
Both expose exact mathematical nanoseconds, with the type recording the
chosen interpretation. This profile uses the proleptic Gregorian rules
and leaves legacy writer rebasing and Arrow range conversion to other profiles.

[INT96 wire words and interpretation](parquet-int96.md) ·
[Bounded dictionary chunk profile](parquet-int96-dictionary.md)

## File admission and reads

The opener reuses the checked snapshot and flat leaf binder. It applies the
file byte and declared total row budgets. Footer validation requires
nonnegative row-group counts that sum to the declared file count. For each
footer ordinal, the bound column ordinal selects the original chunk, whose
singleton path, INT96 type, declared value count and byte span must agree.
The opener checks the selected spans for overlap by sorting a copy by byte
start. Indexed reads and collection keep the original footer order.

The open check covers the footer and selected intervals. Each group read
checks its own framed payload, count and resource limits. Every chunk must
use codec 0 and contain one leading PLAIN dictionary followed by
RLE_DICTIONARY data pages. V1 and V2 may coexist in one chunk. Each read
decodes its own dictionary and admits only encoding 8 for data pages.
Unselected column payloads are outside the read.

`Checked.readGroup` returns the ordered nullable slot list at one footer
ordinal. `Checked.readAll` publishes only complete groups and stops at the
first failed group. A chunk error retains the group and column ordinals,
the bound name and the original chunk cause. Frame errors reported by the
chunk decoder keep the frame ordinal and absolute header offset. Malformed
dictionary words keep their entry index. Missing references keep the
logical slot and bad dictionary index, including preceding null slots.
A framing error retains its original structural cause at the chunk boundary.

## Contracts

- `openFile_snapshot` ties the binding to the exact checked source and
  bounded footer count. `openFile_disjoint` relates each footer index to
  its entry in the pairwise disjoint selected-span catalogue.
- `select_sound` identifies the retained group and original matched
  column. `readGroup_of_selected` gives the exact decoder call and error
  wrapper. `readGroup_wire` identifies the frames returned by the original
  parser, the leading dictionary, the in-order data decodes and the
  flattened slots at the declared group count.
- `readAll_sound`, `readAll_complete` and `readAll_first_error` characterize
  collection over footer ordinals, including the complete prefix and
  unchanged first failure.

[Theorem header](../../Silmaril/Formats/Parquet/Int96/Dictionary/File/Thms.lean)

## Fixtures

CPython 3.13.5 and PyArrow 26.0.1 generate a required V1 file with signed
Int64 nanosecond endpoints and an optional V2 file with negative subsecond
values, nulls and a microsecond value denoting 10^19 nanoseconds. Each file
has an INT32 column before the selected leaf and three groups with distinct
dictionaries. PyArrow reads all six selected groups. Thrift 0.25.0 checks
page versions, original offsets, ordered 12-byte words and packed
dictionary indices independently. The 10^19 nanosecond observation is
derived from raw words and PyArrow microseconds.

Pinned V2 derivatives corrupt a dictionary word and, separately, the
reference at logical slot 3 after a null in group 1. The Lean guards check
both explicit policies and the exact complete prefix and typed causes.
Other derivatives break only the unselected column, alias two selected
footer intervals, or swap two footer groups while leaving their page
bytes in place. The guards also check selection and limits, and reject
a PLAIN-only file.

[Fixture generator and SHA-256 pins](../../scripts/parquet-int96-dictionary-file/check-fixtures.py) ·
[Lean guards](../../Silmaril/Formats/Parquet/Int96/Dictionary/File/Tests.lean) ·
[Pinned wheels](../../tests/formats/columnar-timestamp-wire/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Parquet.Int96.Dictionary.File.Tests
make check CHECK_TARGETS='+Silmaril.Formats.Parquet.Int96.Dictionary.File.Tests'
lake env lean -DautoImplicit=false -DwarningAsError=true scripts/parquet-int96-dictionary-file/Axioms.lean
python3 -m venv /tmp/parquet-int96-dictionary-file
/tmp/parquet-int96-dictionary-file/bin/pip install --no-deps --require-hashes -r tests/formats/columnar-timestamp-wire/requirements.txt
/tmp/parquet-int96-dictionary-file/bin/python -I scripts/parquet-int96-dictionary-file/check-fixtures.py
```
