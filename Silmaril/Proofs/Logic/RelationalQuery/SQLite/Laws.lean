module

public import Silmaril.Logic.RelationalQuery.SQLite.Defs
import Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Thms

public section

namespace Silmaril.SQLite.Relational.CatalogExecutor

open Silmaril.Relational

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

private theorem eval_lookup (target : Target sem) (key : Int64) (test : SqlValue → Bool) :
    (target.table.rows.any fun row => row.rowId? == some key && test (row.get target.column)) =
      (target.lookup key).any test := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq, Option.any_eq_true]
  constructor
  · rintro ⟨row, inTable, rowid, passed⟩
    exact ⟨row.get target.column, (target.lookup_iff key _).mpr ⟨row, inTable, rowid, rfl⟩, passed⟩
  · rintro ⟨value, lookup, passed⟩
    obtain ⟨row, inTable, rowid, rfl⟩ := (target.lookup_iff key _).mp lookup
    exact ⟨row, inTable, rowid, passed⟩

private theorem denote_of_execute (db : Connection (profile sem)) (call : Invocation Names)
    (expected observed : SelectResult SqlValue)
    (evaluated : (execute sem db call).1 = .statement (.ok expected)) :
    (∃ after, denote sem db call (.statement (.ok observed), after)) ↔ observed = expected := by
  rw [← execute_eq sem]
  constructor
  · rintro ⟨_, h⟩
    have resultEq := congrArg Prod.fst h
    rw [evaluated] at resultEq
    cases resultEq
    rfl
  · rintro rfl
    exact ⟨(execute sem db call).2, Prod.ext evaluated rfl⟩

namespace PointRead.Proofs

variable {snapshot : SqlSnapshot sem}

theorem execute_pointRead (db : Connection (profile sem)) (read : PointRead db.catalog)
    (key : Int64) : (execute sem db (read.invocation key)).1 = .statement (.ok (read.result key)) := by
  have htable : db.catalog.tables read.table.val = some ⟨read.target.schema, read.target.table⟩ :=
    (Option.some_get _).symm
  have hfind : read.target.schema.findColumn read.columnName = some read.column := read.found
  have hrowid : read.target.schema.resolvesRowId "rowid" = true := read.rowIdVisible
  have hordinary : read.target.schema.generation read.column = none := read.ordinary
  have admitted : classify db.catalog (read.invocation key) = .invoke (read.invocation key) := by
    simp [classify, invocation, htable, hfind, hrowid, Option.any, hordinary]
  have resolved : resolve db.catalog (read.invocation key).statement =
      .ok ⟨read.target, read.target.schema.name read.column⟩ := by
    simp only [resolve, invocation, htable, hfind]
    rfl
  unfold execute
  rw [admitted]
  simp only [Executor.check, CheckedOutcome.ofStatement, Executor.execute, Executor.prepare, executor, resolved]
  simp [invocation, Prepared.bindInt64, Executor.run, readOutcome, ReadOutcome.finish, result]

theorem denote_pointRead (db : Connection (profile sem)) (read : PointRead db.catalog)
    (key : Int64) (observed : SelectResult SqlValue) :
    (∃ after, denote sem db (read.invocation key) (.statement (.ok observed), after)) ↔
      observed = read.result key :=
  denote_of_execute db _ _ _ (execute_pointRead db read key)

theorem eval_sentence (read : PointRead snapshot) (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.eval (queryModel snapshot) (read.sentence key test) = (read.result key).cell.any test :=
  eval_lookup read.target key test

theorem sat_iff_denote (db : Connection (profile sem)) (read : PointRead db.catalog)
    (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.eval (queryModel db.catalog) (read.sentence key test) = true ↔
      ∃ result after, denote sem db (read.invocation key) (.statement (.ok result), after) ∧
        result.cell.any test = true := by
  rw [eval_sentence]
  constructor
  · intro accepted
    obtain ⟨after, observed⟩ := (denote_pointRead db read key _).mpr rfl
    exact ⟨_, after, observed, accepted⟩
  · rintro ⟨result, after, observed, accepted⟩
    rw [← (denote_pointRead db read key result).mp ⟨after, observed⟩]
    exact accepted

end PointRead.Proofs

namespace CatalogPointRead.Proofs

variable {catalog : TableCatalog Affinity Expr}

private theorem unpacked_entry {Schema : Type} {Tables : Schema → Type}
    {entry : Option (Sigma Tables)} {schema : Schema} (found : entry.map Sigma.fst = some schema) :
    entry = some ⟨schema,
      cast (congrArg (Database.Payload Tables) found) (Database.unpackPayload entry)⟩ := by
  cases entry with
  | none => contradiction
  | some entry =>
    obtain rfl := Option.some.inj found
    rfl

private theorem packed_target (read : CatalogPointRead catalog) (snapshot : SqlSnapshot sem)
    (compatible : snapshot.catalog.tables = catalog) :
    snapshot.tables read.table.val = some ⟨read.schema, (read.target snapshot compatible).table⟩ := by
  subst catalog
  exact unpacked_entry (Option.some_get _).symm

theorem classify_invocation (read : CatalogPointRead catalog) (snapshot : SqlSnapshot sem)
    (compatible : snapshot.catalog.tables = catalog) (key : Int64) :
    classify snapshot (read.invocation key) = .invoke (read.invocation key) := by
  have found : read.schema.findColumn read.columnName = some read.column := read.found
  have rowid : read.schema.resolvesRowId "rowid" = true := read.rowIdVisible
  have ordinary : read.schema.generation read.column = none := read.ordinary
  simp [classify, invocation, packed_target read snapshot compatible, found, rowid, Option.any, ordinary]

theorem resolve_invocation (read : CatalogPointRead catalog) (snapshot : SqlSnapshot sem)
    (compatible : snapshot.catalog.tables = catalog) (key : Int64) :
    resolve snapshot (read.invocation key).statement =
      .ok ⟨read.target snapshot compatible, read.schema.name read.column⟩ := by
  have found : read.schema.findColumn read.columnName = some read.column := read.found
  simp only [resolve, invocation, packed_target read snapshot compatible, found]
  rfl

theorem execute_pointRead (read : CatalogPointRead catalog) (db : Connection (profile sem))
    (compatible : db.catalog.catalog.tables = catalog) (key : Int64) :
    (execute sem db (read.invocation key)).1 = .statement (.ok (read.result db.catalog compatible key)) := by
  unfold execute
  rw [classify_invocation read db.catalog compatible]
  simp only [Executor.check, CheckedOutcome.ofStatement, Executor.execute, Executor.prepare, executor,
    resolve_invocation read db.catalog compatible]
  simp [invocation, Prepared.bindInt64, Executor.run, readOutcome, ReadOutcome.finish, result]

theorem eval_sentence (read : CatalogPointRead catalog) (snapshot : SqlSnapshot sem)
    (compatible : snapshot.catalog.tables = catalog) (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.eval (queryModelOfSnapshot snapshot compatible) (read.sentence key test) =
      (read.result snapshot compatible key).cell.any test :=
  eval_lookup (read.target snapshot compatible) key test

theorem sat_iff_denote (read : CatalogPointRead catalog) (db : Connection (profile sem))
    (compatible : db.catalog.catalog.tables = catalog) (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.eval (queryModelOfSnapshot db.catalog compatible) (read.sentence key test) = true ↔
      ∃ result after, denote sem db (read.invocation key) (.statement (.ok result), after) ∧
        result.cell.any test = true := by
  rw [eval_sentence]
  have observed (result : SelectResult SqlValue) :=
    denote_of_execute db _ _ result (execute_pointRead read db compatible key)
  constructor
  · intro accepted
    obtain ⟨after, denoted⟩ := (observed _).mpr rfl
    exact ⟨_, after, denoted, accepted⟩
  · rintro ⟨result, after, denoted, accepted⟩
    simpa only [(observed result).mp ⟨after, denoted⟩] using accepted

end CatalogPointRead.Proofs
end Silmaril.SQLite.Relational.CatalogExecutor
