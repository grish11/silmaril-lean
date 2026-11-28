# Import selected Parquet columns into a mixed named table

`Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet.importNamed`
composes the [selected Parquet-to-IPC converter][converter] with the
[checked mixed IPC named import][importer]. It accepts the same immutable
Parquet carrier, selected INT32 and BYTE_ARRAY leaves, declared layouts,
and source limits as the converter. The supported source is its
uncompressed flat PLAIN profile with Data Page V1 and V2. The destination
schema is derived from the two selected fields in INT32-then-BinaryView
order, retaining exact names and required/optional flags.

Both IPC steps use the same native limits. Successful conversion and
a wire length within the importer cap guarantee a checked observation
of every footer-ordered source group under the derived descriptor.
The IPC observation has one batch per group, including an admitted
empty group. The table flattens the groups in order and retains each
row's signed Int32 and nullable opaque octets. The composition handles
schema-only input through the same empty observation.

The converter runs before the named gate. Source and native writer
errors retain their original typed causes, including any group, column
or page index. After conversion, name conflicts and IPC limits retain
the checked importer's precedence and typed causes. Success requires a
vacant destination and changes only the selected key. Errors return
without a database result, including a late source failure after
earlier groups have decoded.

The [oracle][oracle] regenerates seven pinned inputs using the existing
PyArrow 26.0.1 and Thrift 0.25.0 fixture producer. It compares six actual
Lean inserts with independent PyArrow reads of the original selection,
including a zero-row middle group, null versus empty octets, and a
successful selection beside a corrupt unselected leaf. Six failure
controls cover source admission, exact late read errors, indexed writer
limits, IPC carrier caps and occupied destinations. A separate success
checks the inclusive IPC cap.

```sh
lake build --wfail +Silmaril.Formats.Relational.NamedTable.MixedIpc.FromParquet.Checks
python3.13 scripts/parquet-mixed-named-oracle/check.py --out /tmp/parquet-mixed-named
```

[converter]: parquet-mixed-to-ipc.md
[importer]: arrow-mixed-named-table.md
[oracle]: ../../scripts/parquet-mixed-named-oracle/check.py
