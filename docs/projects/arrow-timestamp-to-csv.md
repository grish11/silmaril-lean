# Arrow TIMESTAMP streams to a named table and typed UTF-8 CSV

`Arrow.TimestampStream.ToCsv.convert` reads the checked one-column IPC V5
TIMESTAMP profile through explicit EOS. It takes an immutable byte stream,
a database, a vacant destination name, IPC limits, and separate CSV row and
byte caps. Success returns the exact named update, typed schema, and UTF-8
CSV bytes together.
[Entry point](../../Silmaril/Formats/Arrow/TimestampStream/ToCsv/Defs.lean) ·
[Checked IPC profile](arrow-timestamp-stream.md)

The schema preserves the field name, unit (seconds, milliseconds,
microseconds, or nanoseconds), nullability, and the timezone annotation
retained by the Arrow reader, including an explicitly empty annotation.
Timestamp values are local readings for absent or empty annotations and
UTC instants for nonempty annotations. Annotation text remains opaque.

Bare CSV carries only the field name and the tagged tick counts. The
separately returned typed schema supplies the unit, zone, and nullable flag
for reimport. `N` denotes null. `T` followed by canonical signed Int64
decimal denotes a present tick in the declared unit. The decimal codec
checks the signed 64-bit range and the exact spelling. The CSV keeps the
original signed tick counts, including fractional-second units and both
signed endpoints.
[Typed UTF-8 CSV](typed-utf8-csv.md)

The adapter checks name occupancy first. It preserves the original indexed
IPC error on a failed read. Empty batches contribute zero rows and successive
batches contribute rows in wire order. The row cap is checked after the IPC
read and before CSV encoding. The byte cap is checked on the encoded CSV
before returning the result. A failed read, export, or cap returns its error
alone.
[Public laws](../../Silmaril/Formats/Arrow/TimestampStream/ToCsv/Thms.lean)

`rows_order` identifies the exact flattened slots. `convert_readback`
identifies the named insertion and recovers its exact typed rows by decoding
with the returned schema. `convert_of_read` gives a sufficient completion
condition from a successful read, representable typed export, and both caps.

The oracle uses the same pinned producer corpus as the wire reader. PyArrow
26.0.1 supplies and checks the retained descriptors and signed raw ticks.
CPython 3.13.5 independently computes the canonical CSV rows. The checks
cover all four units, zoned and local schemas, a non-nullable field, empty
and multiple batches, signed endpoints, a schema-only stream, indexed late
IPC failure, missing EOS, name occupancy, and writer limits.
[Oracle](../../scripts/arrow-timestamp-csv-oracle/check.py) ·
[Pinned PyArrow and NumPy requirements](../../tests/formats/arrow-ipc/requirements.txt)

```sh
lake build --wfail +Silmaril.Formats.Arrow.TimestampStream.ToCsv.Checks
make check CHECK_TARGETS='+Silmaril.Formats.Arrow.TimestampStream.ToCsv.Checks +Silmaril.Formats.Csv.Typed.Codecs.Tests'
python3.13 -m pip install --require-hashes -r tests/formats/arrow-ipc/requirements.txt
python3.13 -I scripts/arrow-timestamp-csv-oracle/check.py --out /tmp/silmaril-timestamp-csv
```
