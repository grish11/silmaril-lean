# Typed Parquet DATE events

`Silmaril.Formats.Parquet.Date.Events.batchReader` opens a one-column Parquet
DATE file as a typed Arrow event source. Open checks one immutable snapshot
and binds its DATE annotation once. Its cursor uses the footer's row-group
ordinals. Each pull uses the same `Date.Checked.readGroup` as the single-group
file entry point and forwards one ordered nullable Date32 batch. The logical
schema retains the admitted leaf name and its required or optional repetition.
The underlying signed INT32 word is already an Arrow Date32 epoch-day payload.
[DATE binder and physical profile](parquet-date-binding.md)

`readAll` pulls through EOF or the first error. An open failure carries the
DATE binder error before any schema appears. A group failure preserves the
completed prefix and wraps the original cause with its zero-based index.
The default PLAIN INT32 scanner still rejects page CRCs. A bounded pull closes
the unread suffix without decoding it. `Arrow.Events.EventStream.collect`
provides the typed table observation with the same terminal outcome. This
adapter emits abstract Arrow events. IPC byte writing is a separate layer.
[Generic Arrow event API](../../Silmaril/Formats/Arrow/Events/Defs.lean)

`Date.openChecked_ok_iff` ties the capability to one checked snapshot and
its annotation. `Checked.readGroup_of_opened` and `rowsAt_eq_readGroup`
connect the event pull to the existing selected-group API. `batch_slots`
preserves each nullable slot in order. `readAll_eof_iff` characterizes the
exact ordered batches at EOF, `readAll_first_error` identifies the complete
preceding batches and the typed failure, and `read_prefix_closed`
characterizes bounded close using only the attempted prefix.
[Theorem headers](../../Silmaril/Formats/Parquet/Date/Events/Thms.lean)

## Verification

The existing pinned PyArrow 26.0.1 DATE fixture supplies two row groups with
signed endpoints, year zero, null, and leap day. PyArrow independently reads
each complete group as Date32. The damaged control changes the second group's
one-byte PLAIN encoding to RLE_DICTIONARY with Apache Thrift 0.25.0 and
preserves file and page extents. PyArrow reads the first group and rejects the
second. The event oracle checks full EOF, the exact late error and retained
prefix, and successful close after one pull on the damaged file. It also checks
required-field nullability, default CRC rejection and malformed-annotation
open failure. Each successful event trace is checked through standard table
collection as well. [Fixture manifest](../../scripts/parquet-date-oracle/fixtures.json)
· [Oracle](../../scripts/parquet-date-oracle/check.py)

```sh
targets='+Silmaril.Formats.Parquet.Date.Events.Thms +Silmaril.Formats.Parquet.Date.Events.Tests +Silmaril.Formats.Parquet.Date.Tests parquet-flat-scan-regression'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
python3 -I scripts/parquet-date-oracle/check.py --events
```

Use `--pyarrow-path` and `--thrift-path` for separately unpacked pinned wheels.
