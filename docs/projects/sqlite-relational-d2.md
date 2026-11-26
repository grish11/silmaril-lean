# SQLite relational schemas and catalog (Track D2)

Import `Silmaril.Semantics.SQLite.Relational.Catalog.Thms` for the schema, table
and catalog interfaces in `Silmaril.SQLite.Relational`. D2 instantiates the
typed rows, aligned columns and databases from [Track C](relational.md).

## Upstream reference

The reference is SQLite **3.54.1**, public source tree
`57520227c95396ce39ba6ecaac8d475b78dd3964` in the Git mirror, with Fossil
artifact `555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76`.
SQLite tokenizes and parses SQL, generates bytecode, then runs it through a
virtual machine over the B-tree, pager and OS interface. D2 starts with
resolved schema declarations and logical rows. Its contracts describe that
logical layer. [Architecture](https://sqlite.org/arch.html) ·
[Release source](https://github.com/sqlite/sqlite/tree/57520227c95396ce39ba6ecaac8d475b78dd3964) ·
[Source artifact](https://sqlite.org/src/info/555e07ef33f69a0957d24d8e555b702464a131d6f1607f4c3c1e4551e8e6ca76)

## Interface for query semantics

| Import suffix | Declarations and guarantees |
| --- | --- |
| `Schema.Thms` | `TableSchema` records table mode, ordered uniquely named columns, affinities, organization, keys and expression handles. `findColumn` resolves an exact normalized name to a `Fin schema.width`. `namedPositional` supplies Track C's named schema and its positional interpretation. |
| `Table.Thms` | `TableRow.get` reads a value, `TableRow.rowId?` reads an optional signed rowid, and `CheckedTable.rows` reads the ordered row list. `column` returns storage-typed cells and `columnValues` observes their values. `materialize` computes generated cells from storage-typed supplied cells. `CheckedTable.check` certifies an existing row list and is decidable with `DecidableEq` on the value type. |
| `Catalog.Thms` | `PackedDatabase` maps a normalized table name to `Option (Σ schema, CheckedTable model sem schema)`. `DependentDatabase` holds the same tables over a separate `TableCatalog`. `Snapshot.catalog` returns the table schemas and `CatalogObjects`. `CheckedSnapshot` additionally certifies foreign keys across tables. |

## Mode, keys and constraints

- Dynamic declarations use the injected affinity on write. Ordinary `ANY`
  uses NUMERIC affinity. STRICT declarations restrict the declared name and
  the stored type. A STRICT `ANY` column preserves the input exactly,
  including its storage class. SQL NULL passes the type check and is
  subject to the table's constraints. The injected `ValueModel` supplies
  bounded coercions and can report failure.
  [Datatypes](https://sqlite.org/datatype3.html) ·
  [STRICT tables](https://sqlite.org/stricttables.html) ·
  [Affinity and primary-key resolution](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/build.c#L1711) ·
  [VDBE type checks](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/vdbe.c#L3438)
- ROWID snapshots carry distinct signed 64-bit rowids. A resolved INTEGER
  PRIMARY KEY alias must agree with its rowid. WITHOUT ROWID snapshots
  require a declared primary key with no NULL components and have no
  observable rowid. STRICT primary keys also require non-NULL components.
  Ordinary non-alias ROWID primary keys admit NULL unless a separate
  NOT NULL constraint applies. Row order is an explicit observation of the
  input snapshot. Identifier normalization, alias resolution including the
  inline DESC exception, rowid allocation, AUTOINCREMENT and scan order
  are outside the snapshot model.
  [ROWID tables](https://sqlite.org/rowidtable.html) ·
  [WITHOUT ROWID](https://sqlite.org/withoutrowid.html) ·
  [CREATE TABLE](https://sqlite.org/lang_createtable.html)
- NOT NULL checks each declared column. CHECK accepts true or SQL NULL.
  Evaluation failure rejects the row. PRIMARY KEY and UNIQUE checks
  compare pairs of rows through the profile's comparison for each column,
  with any NULL component preventing a uniqueness conflict. A generated
  column is calculated from an explicit ordered list of supplied columns
  and passes through its write coercion. D2 materializes both VIRTUAL and
  STORED values in the same logical row. It keeps the declared storage
  tag but does not model recomputation timing, chained generation, DDL
  expression admission, defaults, or conflict-resolution actions.
  [Generated columns](https://sqlite.org/gencol.html) ·
  [Native row generation](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/insert.c#L285) ·
  [Native constraint emission](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/insert.c#L1891)
- Snapshot foreign-key checking resolves explicit parent column names
  against a declared PRIMARY KEY or table UNIQUE key, requiring the same
  key order and arity. Parent schemas must resolve even for empty child
  tables. For each child row, any NULL component discharges the check.
  Otherwise a parent row must match using the caller's comparison with
  parent affinity and collation. Deferred checks, actions, omitted parent
  column lists, external UNIQUE index eligibility and PRAGMA enforcement
  state are outside this check.
  [Foreign key rules](https://sqlite.org/foreignkeys.html) ·
  [Native foreign key checks](https://github.com/sqlite/sqlite/blob/57520227c95396ce39ba6ecaac8d475b78dd3964/src/fkey.c#L889)

`TableSemantics` supplies pure expression evaluation and key comparisons.
It receives the declared column type and collation for comparisons. The
caller supplies SQL comparison behavior, including parent affinity in foreign
key comparisons. Index, view and trigger declarations record names and
handles. They carry no execution or maintenance behavior. Collation and
function registrations record connection-side names, signatures or
implementation identifiers. Resolving overloads, dispatching callbacks and
validating object definitions are outside D2. The catalog has one resolved
database namespace, with no attached databases, temp lookup or
`sqlite_schema` row encoding.
[Schema table](https://sqlite.org/schematab.html) ·
[Indices](https://sqlite.org/lang_createindex.html) ·
[Views](https://sqlite.org/lang_createview.html) ·
[Triggers](https://sqlite.org/lang_createtrigger.html) ·
[Collations](https://sqlite.org/c3ref/create_collation.html) ·
[Application-defined functions](https://sqlite.org/appfunc.html)

## Checked conversions and erasure

- `CheckedTable.rowsEquivColumns` preserves every cell and row identity in
  sequence. The aligned payload carries the same validity certificate after
  transposition. `materialize_restrict_iff` recovers exactly the generated
  values of a generation-valid row from its supplied cells under the same
  schema and evaluator. `generationValid_iff` states the agreement with
  Track C's generation predicate.
- `databaseEquiv` and `packedRowsEquivColumns` preserve the table catalog.
  `erase_columns` and `erase_constraints` commute with row-only
  observation. Absent names erase to `none` and present-empty tables erase
  to `some []`. The checked examples exhibit equal erasures of different
  empty schemas and equal row observations from distinct rowids at a fixed
  schema.
- `eraseKeepingIdentity` retains the schema, ordered row identities and
  exact values. At a fixed value and evaluation profile, proof irrelevance
  and positional read-back make that observation injective on packed table
  entries. `recover_eraseKeepingIdentity` uses Track C's unique-preimage
  recovery. It is a logical round trip using classical choice. The encoding
  covers the packed tables. Other catalog declarations travel separately in
  `Snapshot.objects`.

The model provides no equivalence theorem for the SQLite C engine, bytecode,
file format, query planner or transaction behavior.

## Checks

```sh
lake build --wfail +Silmaril.Semantics.SQLite.Relational.Catalog.Examples
scoped=$(make -s scope BASE=origin/main)
targets=$(python3 scripts/ci-targets.py --scoped "$scoped" --full "$(make -s scope)")
make check CHECK_TARGETS="$targets"
```
