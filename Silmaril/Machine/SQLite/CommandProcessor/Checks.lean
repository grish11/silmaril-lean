module

import Silmaril.Machine.SQLite.CommandProcessor.Thms

namespace Silmaril.Machine.SQLite.CommandProcessor.Checks

open Silmaril.SQLite.Relational

private def semantics : TableSemantics SqlValue Affinity Unit where
  evalGenerated _ _ := none
  evalCheck _ _ := none
  keyEqual _ _ a b := decide (a = b)
  foreignEqual _ _ a b := decide (a = b)

private def schema (name : String) : TableSchema Affinity Unit where
  mode := .dynamic
  width := 1
  column _ := ⟨name, .dynamic none .blob, none, false⟩
  uniqueNames := fun {_ _} _ => Subsingleton.elim _ _
  organization := .rowid none
  generation _ := none
  suppliedExists := ⟨0, rfl⟩
  inputsSupplied := by simp
  primaryKeySupplied := by simp
  organizationKey := trivial

private def emptyTable (name : String) :
    Option (Σ s, CheckedTable ValueModel.sqlValue semantics s) :=
  (CheckedTable.check (schema := schema name) []).map fun table => ⟨schema name, table⟩

private def connection : State semantics where
  catalog := {
    tables
      | "items" => emptyTable "value"
      | "shadow" => emptyTable "rowid"
      | _ => none
    objects := { views := fun name => if name = "v" then some ⟨["value"], ()⟩ else none } }
  backing := ()
  cache := ()

private def observe (text : String) : Except PrepareError (String × Option Int64) :=
  (prepare connection text).map fun p => (p.plan.label, p.key)

example : observe "Select VALUE\nFROM Items Where ROWID=?1;\t" = .ok ("value", none) := by cbv

example : observe "select value from items where rowid = ?2" =
    .error (.text (.lexical .outsideFragment)) := by cbv

example : observe "select value from items where rowid = ?1;;" =
    .error (.text .outsideGrammar) := by cbv

example : observe "select value from items where value = ?1" =
    .error (.text .outsideGrammar) := by cbv

example : observe "select value from missing where rowid = ?1" =
    .error (.planner (.resolve (.missingTable "missing"))) := by cbv

example : observe "select missing from items where rowid = ?1" =
    .error (.planner (.resolve (.missingColumn "items" "missing"))) := by cbv

example : observe "select missing from shadow where rowid = ?1" =
    .error (.planner (.unsupported "rowid predicate")) := by cbv

example : observe "select value from v where rowid = ?1" =
    .error (.planner (.unsupported "view")) := by cbv

end Silmaril.Machine.SQLite.CommandProcessor.Checks
