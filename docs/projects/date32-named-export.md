# Selected named Date32 columns to native Parquet DATE

`NamedTable.Date32.Export.convert` reads an existing
`NamedTable.Date32.Database` entry using `Scan.observePacked`. The caller
supplies the database key, a zero-based column ordinal, and the exact
expected field name and nullability. An ordinal disambiguates repeated
labels. The source table may have other Date32 columns. The type of
this database fixes all columns to Date32. A different selected kind
means different declared nullability, and a stored null in a required
column fails before page emission.
[Named import and carrier](date32-named-import.md)
· [Export definitions](../../Silmaril/Formats/Relational/NamedTable/Date32/Export/Defs.lean)

Admission checks the name lookup, ordinal, field name, Date32 kind and
total row cap in that order. A successful selection reads that position
in each row of the existing ordered list, preserving repeats and nulls.
The same native group writer used by the single-batch IPC converter
writes the selected slots directly into one checked Parquet INT32 DATE
group. It uses the caller's separate writer and DATE readback limit
records. It preserves the full signed Int32 day domain and emits both the
modern DATE annotation and matching ConvertedType DATE. An empty named
table emits one explicit zero-row group.
[Native DATE writer profile](arrow-date32-to-parquet.md)
· [Pinned Parquet DATE semantics](https://github.com/apache/parquet-format/blob/04d56f291ff963e98bc37ab8100e2fc133ff583c/LogicalTypes.md#date)

`select_eq_ok_iff` identifies the stored table, descriptor, row cap and
exact ordered positional projection. The selection error laws give the
typed lookup, schema, kind and row-limit results. `convert_eq_ok_iff`
requires successful selection and native writer admission.
`convert_readback` bounds the returned file extent and recovers the exact
field and annotation, one group, and every signed nullable slot in the
selected column. `convert_selectError` and `convert_writeError` preserve
the original stage and cause.
[Theorem header](../../Silmaril/Formats/Relational/NamedTable/Date32/Export/Thms.lean)

## Independent checks

PyArrow 26.0.1 produces an optional two-group DATE file with both signed
Int32 endpoints, a null, negative days and a repeated date, and a required
schema-only DATE file. The existing named import reads each file into the
packed database before export. A third fixture selects the second of two
identically named Date32 columns from a populated table. PyArrow reads all
three resulting Parquet files and checks the exact schema, group count
and ordered signed slots. Apache Thrift 0.25.0 checks raw annotations
and the exact PLAIN V1 page header and body. Native guards exercise
missing keys, invalid ordinals, field/kind mismatches, required null,
and the separate table row, file byte and checked readback budgets.
[Fixture hashes](../../scripts/named-date32-parquet-oracle/fixtures.json)
· [Oracle](../../scripts/named-date32-parquet-oracle/check.py)

```sh
targets='+Silmaril.Formats.Relational.NamedTable.Date32.Export.Thms +Silmaril.Formats.Relational.NamedTable.Date32.Export.Tests'
lake build --wfail $targets
make check CHECK_TARGETS="$targets"
lake env lean -DautoImplicit=false -DwarningAsError=true tests/formats/named-date32-parquet/Axioms.lean
python3 -I scripts/named-date32-parquet-oracle/check.py
```

The oracle accepts `--pyarrow-path` and `--thrift-path` for separately
unpacked pinned wheels.
