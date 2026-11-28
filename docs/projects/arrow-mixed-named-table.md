# Mixed Int32 and BinaryView IPC to a named table

`Silmaril.Formats.Relational.NamedTable.MixedIpc.importIpc db name expected limits input`
consumes a bounded Arrow IPC V5 stream with exactly one primitive Int32 and
one BinaryView field. Either field order is allowed. The destination
descriptor specifies that order, both names and both nullability flags.
Column identities in the shared table schema are pairs of name and
nullability. The two value kinds are signed `Int32` and raw `List UInt8`,
each wrapped in an option by the nullable table model. Column positions
carry identity even when names repeat.

The adapter reuses `Arrow.MixedFlat.Stream.read`, including its schema,
physical layout, row/cell and view-buffer limits and exact modern EOS
check. A separate caller-supplied cap bounds the size of the in-memory
IPC carrier. After successful exhaustion the adapter checks the two
column constructors, matches their labels to the decoded schema, and
checks both lengths against the decoded row count before pairing
positions. Binary values preserve every octet. Null, an empty value,
embedded zero and non-UTF-8 payloads remain distinct.

`MixedIpc.read` exposes one list of paired slots per checked record batch.
A schema-only stream yields `[]` and one empty batch yields `[[]]`.
The database stores the concatenated rows. At the same schema these
two streams therefore insert equal empty tables, and an empty middle
batch contributes zero rows. The named insertion gate gives precedence
to vacancy, then source success, then exact expected schema. An occupied
name, a source failure or a descriptor mismatch yields a typed error
with no updated database. A late native failure carries its original
zero-based batch position and cause. This is an all-or-error import
over an in-memory carrier.

The [Arrow 24.0.0 columnar format][columnar] specifies the IPC stream,
the little-endian Int32 layout and the variable-size binary view layout.
The native parser targets the V5 structures in the pinned [Schema][schema]
and [Message][message] files. The [oracle][oracle] regenerates seven pinned
streams with PyArrow 26.0.1 on little-endian hosts. It compares exact
fields, batch counts and inserted nullable rows using both field orders,
signed Int32 endpoints, empty and opaque octets, a repeated row, and
schema-only, explicit empty-batch and empty-middle shapes. Refusals cover
typed late truncation, missing EOS, trailing bytes, row and input caps,
unsupported Utf8View, exact descriptor differences and vacancy
precedence. Successful insertions verify that an existing row at a
different name survives and that a repeated insertion conflicts.

```sh
lake build --wfail +Silmaril.Formats.Relational.NamedTable.MixedIpc.Checks
python3 scripts/arrow-mixed-named-oracle/check.py --out /tmp/arrow-mixed-named
```

[columnar]: https://arrow.apache.org/docs/24.0/format/Columnar.html
[schema]: https://github.com/apache/arrow/blob/apache-arrow-24.0.0/format/Schema.fbs
[message]: https://github.com/apache/arrow/blob/apache-arrow-24.0.0/format/Message.fbs
[oracle]: ../../scripts/arrow-mixed-named-oracle/check.py
