# Typed batch events to named tables and UTF-8 CSV

`Silmaril.Formats.Csv.EventStream.convert` accepts a typed Arrow event stream,
an existing named database, a destination name, an expected ordered schema,
and one cell codec per kind. It collects the stream, uses the established named
insertion policy, and exports the inserted table through the named UTF-8 CSV
writer. Success returns the updated database, observed schema, and complete
CSV bytes together. [Named UTF-8 CSV](named-utf8-csv.md)

The terminal outcome must be EOS. Collection concatenates rows in batch order
and preserves the order within each batch. Empty batches contribute no rows.
The exact schema includes the ordered labels and types. A vacant name and a
successful export are required. The new database differs only at that name.
The writer retains the typed null and present tags and the zero-column record
count policy. Wire restrictions apply to the complete header and tagged cells.
[Typed UTF-8 CSV](typed-utf8-csv.md)

Input errors preserve the existing typed named-insertion error, including open,
read, close, name conflict, and schema errors. As in named insertion, an
occupied name takes precedence. A late read error can carry a prefix in the
source observation. Conversion reports the error without returning CSV bytes or
a database update. An export failure likewise returns just the typed output
error, including `unrepresentableWire` for bytes outside the profile. These are
pure, in-memory functions returning an `Except` result.

`convertCollected` accepts an already-collected observation, which lets physical
adapters keep their own validation and error payloads. `convertParquet` accepts
the existing typed `Parquet.Reader.OpenResult` and consumes it with
`Reader.readAll`. Indexed Parquet producers can also supply an event stream
directly. The conversion depends on the typed source contracts. Physical Arrow
IPC decoding and Parquet row-group assembly are separate producers.

`convertCollected_ok_iff` characterizes success exactly.
`convert_roundTrip` and `convertParquet_roundTrip` prove that decoding the
resulting CSV recovers the ordered source rows when the cell codecs obey
parse-after-print. `convertParquet_eq_denote` identifies the Parquet path with
its full-read denotation. The open, read, schema mismatch, and encoding
contracts specify the exact failure results. [Theorem header](../../Silmaril/Formats/Csv/EventStream/Thms.lean)

```sh
targets='+Silmaril.Formats.Csv.EventStream.Examples +Silmaril.Formats.Csv.NamedTable.Utf8.Examples +Silmaril.Formats.Parquet.Reader.Examples'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
```
