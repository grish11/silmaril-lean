# Checked Arrow DATE value buffers

`Silmaril.Formats.Arrow.DateValues` reads little-endian Date32 and Date64
values into ordered nullable Gregorian dates. It accepts the caller-resolved
Field union tag, Date unit, schema endianness, and field nullability. The tag
must be DATE, the unit must match the selected decoder, and the schema must
declare little endian. The Date IDL defaults an omitted unit to MILLISECOND.
The caller resolves that default and supplies the descriptor. A future
reader-side dispatch can share the checked FlatBuffers access across Date and
Timestamp. [Arrow 26.0.1 Schema.fbs](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/format/Schema.fbs)

`decode` accepts a validity bitmap and a value buffer plus a starting slot
and field node. It checks the complete requested extent, even for null slots,
and uses least-significant-bit validity numbering. An omitted bitmap means all
slots are valid. The reader compares the resulting null count with the node
and checks the field's nullability. Date32 words are signed day counts.
Present Date64 words must be exact whole-day signed millisecond counts.
A null slot's word is masked; a fractional Date64 word is an error only
when the slot is present. [Arrow Columnar format](https://github.com/apache/arrow/blob/9e5d6978e9acf372cc989aaaf94e863fe8582c90/docs/source/format/Columnar.rst#validity-bitmaps)
· [Scalar date laws](arrow-parquet-date.md)

`decodeBatch` binds an existing checked IPC `RecordBatch` metadata value and
body for one flat DATE column. It requires one node and the ordered bitmap
and values descriptors, checks body bounds and alignment before slicing, and
reads from slot zero in the resulting views. It honors the existing byte and
row limits. Shared Schema FlatBuffers admission and full DATE streams and
files are follow-up integration steps.

The public laws establish the descriptor profile, characterize successful
slot and column decoding, and identify each output index with its corresponding
physical slot and bitmap bit. The batch laws tie the two views and the row
and null counts to the original record metadata. [Theorem header](../../Silmaril/Formats/Arrow/DateValues/Thms.lean)

## Independent fixtures

The harness pins PyArrow 26.0.1 and CPython 3.13.5. It reads PyArrow Date32
and Date64 in-memory slices that cross a validity byte boundary and reproduces
two IPC streams at pinned hashes. PyArrow reads the streams back independently.
Lean checks the original sliced buffers and uses the existing Arrow parser on
the IPC record metadata before binding the body. The harness also checks
Date64 fractional values in present and null slots and rejects wrong units,
wrong endianness, short bitmap and value windows, and an out-of-body descriptor.
Unit and endianness mutations exercise the resolved descriptor API.
[PyArrow fixture pins](../../scripts/arrow-date-values-oracle/fixtures.json)

```sh
targets='+Silmaril.Formats.Arrow.DateValues.Thms +Silmaril.Formats.Arrow.DateValues.Tests +Silmaril.Formats.DateInterop.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
python3 -I scripts/arrow-date-values-oracle/check.py
```

The oracle accepts `--pyarrow-path` for an externally unpacked pinned wheel.
