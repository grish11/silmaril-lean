module

import Silmaril.Logic.RelationalQuery.SQLite.Thms

namespace Silmaril.SQLite.Relational.CatalogExecutor.QueryChecks

open Silmaril.Relational

private def semantics : TableSemantics SqlValue Affinity Unit where
  evalGenerated _ _ := none
  evalCheck _ _ := none
  keyEqual _ _ a b := decide (a = b)
  foreignEqual _ _ a b := decide (a = b)

private def schema : TableSchema Affinity Unit where
  mode := .dynamic
  width := 1
  column _ := ⟨"value", .dynamic none .blob, none, false⟩
  uniqueNames := fun {_ _} _ => Subsingleton.elim _ _
  organization := .rowid none
  generation _ := none
  suppliedExists := ⟨0, rfl⟩
  inputsSupplied := by simp
  primaryKeySupplied := by simp
  organizationKey := trivial

private def row (key : Int64) (value : SqlValue) : TableRow ValueModel.sqlValue schema :=
  TableRow.ofCells key (fun _ => ⟨value, rfl⟩)

private def table : CheckedTable ValueModel.sqlValue semantics schema :=
  ⟨[row 7 .null, row 9 (.integer 0)], by decide⟩

private def withTable (payload : CheckedTable ValueModel.sqlValue semantics schema) :
    Connection (profile semantics) where
  catalog := ⟨fun name => if name = "items" then some ⟨schema, payload⟩ else none, {}⟩
  backing := ()
  cache := ()

private def connection := withTable table

private def read : PointRead connection.catalog where
  table := ⟨"items", by decide⟩
  columnName := "value"
  column := (0 : Fin 1)
  found := rfl
  rowIdVisible := rfl
  ordinary := rfl

private def isNull : SqlValue → Bool
  | .null => true
  | _ => false

example : DatabaseQuery.eval (queryModel connection.catalog) (read.sentence 7 isNull) = true := rfl

example : DatabaseQuery.eval (queryModel connection.catalog) (read.sentence 8 (fun _ => true)) = false := rfl

example : DatabaseQuery.eval (queryModel connection.catalog) (read.sentence 9 (fun _ => true)) = true := rfl

example : DatabaseQuery.eval (queryModel connection.catalog) (read.sentence 9 isNull) = false := rfl

example : ∃ after, denote semantics connection (read.invocation 7)
    (.statement (.ok ⟨"value", some .null⟩), after) :=
  (read.denote_pointRead connection 7 _).mpr rfl

private def declared : TableCatalog Affinity Unit :=
  fun name => if name = "items" then some schema else none

private theorem compatible (payload : CheckedTable ValueModel.sqlValue semantics schema) :
    (withTable payload).catalog.catalog.tables = declared := by
  funext name
  by_cases found : name = "items" <;>
    simp [withTable, Snapshot.catalog, Database.Packed.catalog, declared, found]

private def declaredRead : CatalogPointRead declared where
  table := ⟨"items", by decide⟩
  columnName := "value"
  column := (0 : Fin 1)
  found := rfl
  rowIdVisible := rfl
  ordinary := rfl

private def boundSentence := declaredRead.sentence 7 isNull

private def withoutRow : CheckedTable ValueModel.sqlValue semantics schema :=
  ⟨[row 9 (.integer 0)], by decide⟩

example : DatabaseQuery.eval (queryModelOfSnapshot connection.catalog (compatible table))
    boundSentence = true := rfl

example : DatabaseQuery.eval (queryModelOfSnapshot (withTable withoutRow).catalog (compatible withoutRow))
    boundSentence = false := rfl

example : (execute semantics connection (declaredRead.invocation 7)).1 =
    .statement (.ok ⟨"value", some .null⟩) :=
  declaredRead.execute_pointRead connection (compatible table) 7

example : (execute semantics (withTable withoutRow) (declaredRead.invocation 7)).1 =
    .statement (.ok ⟨"value", none⟩) :=
  declaredRead.execute_pointRead (withTable withoutRow) (compatible withoutRow) 7

end Silmaril.SQLite.Relational.CatalogExecutor.QueryChecks
