# Export a mixed named table to Arrow IPC

`Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.emit db name expected sizes limits`
takes an existing named table with exactly one Int32 and one BinaryView
column in either order. It checks the selected table's positional schema
against the supplied descriptor, including both names and nullability
flags. These are the same descriptors used by the [mixed import][import].
Rows preserve nullable signed Int32 values and raw octets, including null,
empty values, embedded zero and non-UTF-8 payloads.

The caller supplies the ordered batch sizes. Their sum must equal the
stored row count. Each size takes the next contiguous block of rows.
A zero size emits an explicit empty RecordBatch. An empty size list is
valid only for an empty table and emits Schema and EOS. The named table
retains flattened rows, so this policy constructs new batch boundaries.

The adapter reuses the shared named-table splitter and the
[native V5 writer][writer]. It applies the importer's byte cap to the
total raw octets before packing and to the complete output after framing.
Native row, cell, batch and view limits still govern emission. Missing
source names and inconsistent sizes use the shared table errors. Schema,
raw octet and final wire cap failures are separate from native writer
errors, which retain their original causes and batch indices.

Successful emission guarantees exact readback with the same limits.
The checked observation retains the requested batch sizes and yields the
source table when flattened. Import into a vacant destination inserts
that exact table at the selected key. This is an in-memory IPC stream
conversion for the supported mixed profile.

The [independent PyArrow 26.0.1 oracle][oracle] reads five pinned streams
emitted by Lean, checks V5 framing through EOS and checks exact field
order, names, nullability, batch sizes and nullable values. The same checks
exercise Lean read and import, including two plans for the same stored
rows, reversed field order, schema-only, explicit empty and empty-middle
batches. Nine typed refusals cover missing names, inconsistent sizes,
schema mismatches, octet and wire caps, and native value, nullability
and batch limits.

```sh
lake build --wfail +Silmaril.Formats.Relational.NamedTable.MixedIpc.Export.Checks
python3 scripts/arrow-mixed-named-export-oracle/check.py --out /tmp/arrow-mixed-named-export
```

[import]: arrow-mixed-named-table.md
[writer]: arrow-mixed-flat.md
[oracle]: ../../scripts/arrow-mixed-named-export-oracle/check.py
