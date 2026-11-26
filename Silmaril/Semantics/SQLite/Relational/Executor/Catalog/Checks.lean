module

import Silmaril.Semantics.SQLite.Relational.Executor.Catalog.Thms

namespace Silmaril.SQLite.Relational.CatalogExecutor.Checks

private def semantics : TableSemantics SqlValue Affinity Unit where
  evalGenerated _ _ := none
  evalCheck _ _ := none
  keyEqual _ _ a b := decide (a = b)
  foreignEqual _ _ a b := decide (a = b)

private def schema (label : String) : TableSchema Affinity Unit where
  mode := .dynamic
  width := 1
  column _ := ⟨label, .dynamic none .blob, none, false⟩
  uniqueNames := fun {_ _} _ => Subsingleton.elim _ _
  organization := .rowid none
  generation _ := none
  suppliedExists := ⟨0, rfl⟩
  inputsSupplied := by simp
  primaryKeySupplied := by simp
  organizationKey := trivial

private def stored (label : String) (key : Int64) (value : SqlValue) :
    Option (Σ s, CheckedTable ValueModel.sqlValue semantics s) :=
  let row := TableRow.ofCells (schema := schema label) key (fun _ => ⟨value, rfl⟩)
  (CheckedTable.check [row]).map fun checked => ⟨schema label, checked⟩

private def connection : Connection (profile semantics) where
  catalog := {
    tables
      | "items" => stored "value" 7 .null
      | "shadow" => stored "rowid" 7 (.integer 8)
      | _ => none
    objects := {
      views := fun name => if name = "v" then some ⟨["value"], ()⟩ else none } }
  backing := ()
  cache := ()
  session := ⟨false, 2, 3, -4⟩

private def call (table column : String) (key : Int64) : Invocation Names :=
  ⟨⟨⟨table, column⟩⟩, some (1, key)⟩

example : execute semantics connection (call "items" "value" 7) =
    (.statement (.ok ⟨"value", some .null⟩), connection) := rfl

example : execute semantics connection (call "items" "value" 8) =
    (.statement (.ok ⟨"value", none⟩), connection) := rfl

example : execute semantics connection (call "items" "missing" 7) =
    (.statement (.error (.prepare (.missingColumn "items" "missing"))), connection) := rfl

example : execute semantics connection (call "missing" "value" 7) =
    (.statement (.error (.prepare (.missingTable "missing"))), connection) := rfl

example : execute semantics connection (call "shadow" "rowid" 7) =
    (.unsupported "rowid predicate", connection) := rfl

example : execute semantics connection (call "v" "value" 7) =
    (.unsupported "view", connection) := rfl

end Silmaril.SQLite.Relational.CatalogExecutor.Checks
