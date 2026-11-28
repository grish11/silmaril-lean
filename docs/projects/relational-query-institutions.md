# Table and database query institutions

`Silmaril.Logic.RelationalQuery.Thms` exports `TableQuery.institution` and
`DatabaseQuery.institution` as instances of the library's `Inst` structure.
Models are discrete categories on the native Lean data. Satisfaction means
that evaluation returns `true`.
[Public API](../../Silmaril/Logic/RelationalQuery/Thms.lean) · [Relational foundations](relational.md)

## Signatures and models

A `QuerySchema Kind` has an arbitrary type of indices and a kind at each
index. Fixing `Cell : Kind → Type` interprets those kinds as Lean cell types.
A model is a native `Table`, a finite list of dependent `Row` functions.
`QuerySchema.ofPositional` uses the existing positional schema and its column
maps. `QuerySchema.ofNamed` uses occupied names as indices and maps the
existing name-preserving arrows. A `NamedPositionalSchema` can use either
adapter via the existing `forgetNames` or `forgetPositions` functor. Only
kind preservation is required for arrows in the general signature category.
[Definitions](../../Silmaril/Logic/RelationalQuery/Defs.lean) · [Native schema APIs](../../Silmaril/Semantics/Relational/Table/Schema/Defs.lean)

A `QueryCatalog Kind` assigns a table schema to each occupied index. Its
model is a native `Database.Over` with one typed table at each such index.
`QueryCatalog.ofCatalog` and `modelOfOver` adapt partial named catalogs and
their typed payloads. `ofPacked` and `modelOfPacked` read the schema and
payload from each occupied entry of a native packed database. An absent
name has no query index. A present empty table has an index and its row
existence tests return `false`.

The aligned-column adapter uses `AlignedColumns.ofRows` and `toRows`.
`reductColumns` commutes with both conversions, and `evalColumns` agrees with
row evaluation after conversion. A zero-column table retains its row count.
The institution uses finite list rows. A native `Rows RowId` or `Columns RowId`
can supply these when the caller gives a finite order of the row IDs using
`orderRows` and `List.ofFn`. Constraint certificates and generated-column
rules belong to the source models and their adapters. General signature maps
preserve kinds and need no proof of preservation of those rules.
[Column laws](../../Silmaril/Logic/RelationalQuery/Thms.lean) · [Native organization APIs](../../Silmaril/Semantics/Relational/Table/Organization/Defs.lean)

## Sentence grammar and reindexing

```text
q ::= truth Bool | atom a | not q | and q q | or q q
Table atom    ::= a typed row test (Row → Bool)
Database atom ::= an occupied table index paired with a test on that table's Row
```

An atom is true when some row in the indicated list passes its test
(`List.any`). A constant-true test asks whether the table is nonempty.
`not (atom p)` asserts that no row passes `p`. Distinct atoms in an `and`
may have different witnesses, including when both atoms query the same table.
For a one-column natural-number table, this sentence asks whether 7 occurs
and 8 is absent.

```lean
import Silmaril.Logic.RelationalQuery.Thms

open Silmaril.Relational

def oneNumber : QuerySchema Type := ⟨Unit, fun _ => Nat⟩

example : TableQuery.Sentence id oneNumber :=
  .and (.atom fun row => Nat.beq (row ()) 7)
       (.not (.atom fun row => Nat.beq (row ()) 8))
```

In a database with occupied indices `items` and `archive`, the sentence
`.and (.atom ⟨items, fun _ => true⟩) (.not (.atom ⟨archive, fun _ => true⟩))`
asserts that `items` has a row and `archive` is empty.

Table arrows send source columns to target columns of the same kind. Database
arrows also send each occupied source table to a target table and give a
column map for that component. Arrows can repeat or omit target indices.
Sentence translation precomposes each row test with the corresponding pullback,
and the model reduct pulls back rows componentwise. The identity, composition,
and evaluation laws prove the satisfaction condition in both institutions.
`componentCorridor` embeds a table's sentences at any chosen database index
and projects out its model. `translate_select` and `reduct_component` show that
both directions commute with reindexing. The singleton signature functor
packages these corridors as `singletonComorphism`; its models are equivalent
to native tables via `QueryCatalog.singletonModel`.
[Institution laws](../../Silmaril/Logic/RelationalQuery/Thms.lean) · [Checked examples](../../Silmaril/Logic/RelationalQuery/Checks.lean)

Reducts preserve the order and multiplicity of rows, including repeated rows
created by column projection. `eval_eq_of_mem_iff` proves that tables with the
same row membership satisfy the same sentences. Counts, bag equality, ordered
results, cross-row joins, aggregates, updates, errors and divergence are outside
the grammar. Row tests are typed Lean functions. A test can combine conditions
on cells of a single row, and the grammar has no parser or SQL expression
semantics. The existing `QueryRel` and `ResultRows` APIs remain available for
richer observations.
[Query result types](../../Silmaril/Semantics/Relational/Query/Result.lean)

## SQLite point reads

`Silmaril.Logic.RelationalQuery.SQLite.Thms` adds an adapter for the existing
checked snapshot semantics of `SELECT column FROM table WHERE rowid = ?1`.
`PointRead` specifies a present packed table, successful resolution of a named
ordinary column, and visibility of the `rowid` pseudocolumn. It uses the existing
normalized catalog spelling and binds slot 1 to an `Int64`. The adapter uses the
snapshot's native typed rows, including their row identity slot. Each `sentence`
tests for the rowid and applies a caller-supplied Boolean test to its projected
`SqlValue`. `execute_pointRead` identifies the successful interpreter reply,
`denote_pointRead` identifies the same reply in the reference relation, and
`eval_sentence` relates the sentence's truth to `Option.any` on the resulting
cell. `sat_iff_denote` gives the satisfaction equivalence directly for the
reference relation, existentially hiding the final connection.
[Adapter and laws](../../Silmaril/Logic/RelationalQuery/SQLite/Thms.lean) · [Existing point-read semantics](sqlite-relational-d2.md)

`CatalogPointRead` in the same header indexes the projection by the SQLite
`TableCatalog`. Its table name, column and admission checks use only resolved
table declarations. `sentence` binds slot 1 to a signed 64-bit key and takes
a Boolean test on the projected cell. For each snapshot with
`snapshot.catalog.tables = catalog`, `queryModelOfSnapshot` supplies that
snapshot's checked rows at the same signature. This requires equality of the
table declarations and permits different rows and other catalog objects.
`CatalogPointRead.eval_sentence` and `CatalogPointRead.sat_iff_denote` relate
evaluation in each such model to its own checked point-read result.
[Cross-snapshot check](../../Silmaril/Logic/RelationalQuery/SQLite/Checks.lean)

With a constant-true test, a result cell of `some .null` satisfies the sentence,
as does `some (.integer 0)`. A result cell of `none` means no row and makes the
sentence false. A Lean test can explicitly recognize the `.null` constructor.
SQL scalar and `WHERE` truth use different rules, including three-valued NULL
propagation and SQLite coercions, which this bridge does not interpret. It covers
checked snapshots and single-row projections. Unbound or erroneous invocations,
views, generated projections, hidden rowid, native file/VDBE execution and
multi-row results are outside its coverage.

Import `Silmaril.Machine.SQLite.CommandProcessor.Query.Thms` to connect the
catalog sentence to the modeled compiler and VM. `pointRead_sat_iff_execute`
requires a compatible snapshot, a `Parser.Represents` witness for the text and
the declared names, and `CodeGenerator.Represents` at the caller-supplied
location of the resolved target. The VM table must match the checked rows in
order, by signed rowid and by a present projected cell that transfers to the
same `SqlValue`. Under these hypotheses, the sentence holds exactly when the
compiled run with the same bound key returns a cell passing the test.
[Modeled execution theorem](../../Silmaril/Machine/SQLite/CommandProcessor/Query/Thms.lean) · [Point-read compiler](sqlite-point-select.md)

## Verification

```sh
set -- +Silmaril.Logic.RelationalQuery.Checks \
       +Silmaril.Logic.RelationalQuery.SQLite.Checks \
       +Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Checks \
       +Silmaril.Machine.SQLite.CommandProcessor.Execute.Checks
lake build --wfail "$@"
make check CHECK_TARGETS="$*"
```
