module

public import Silmaril.Semantics.SQLite.Relational.Catalog.Thms
public import Silmaril.Semantics.SQLite.Relational.Schema.SqlValue

/-! Executable examples of the storage and constraint checks with D1 values. -/

namespace Silmaril.SQLite.Relational

private def textInput : SqlValue := .text (.utf8 "0007")

example : (DeclaredColumnType.store ValueModel.sqlValue (.strict .any) textInput).map Subtype.val =
    some textInput := by decide

example : (DeclaredColumnType.store ValueModel.sqlValue .dynamicAny textInput).map Subtype.val =
    some (.integer 7) := by decide

example : (DeclaredColumnType.store ValueModel.sqlValue (.strict .int) (.text (.utf8 "unexpected"))).isNone =
    true := by decide

private inductive Expr where
  | next
  | nonNegative

private def sem : TableSemantics SqlValue Affinity Expr where
  evalGenerated
    | .next, [.integer value] => some (.integer (value + 1))
    | _, _ => none
  evalCheck expr row := match expr, (List.ofFn row).head? with
    | .nonNegative, some (.integer value) => some (if value < 0 then .false else .true)
    | .nonNegative, some .null => some .null
    | _, _ => none
  keyEqual _ _ first second := decide (first = second)
  foreignEqual _ _ first second := decide (first = second)

private def inputSchema : TableSchema Affinity Expr where
  mode := .strict
  width := 2
  column i := {name := if i = 0 then "input" else "next", type := .strict .integer}
  uniqueNames := by decide
  organization := .withoutRowid
  generation i := if i = 0 then none else some ⟨.stored, .next, [0]⟩
  suppliedExists := ⟨0, rfl⟩
  inputsSupplied := by
    intro i spec declared j mem
    split at declared
    · contradiction
    · cases declared
      simpa using mem
  primaryKey := some ⟨0, []⟩
  primaryKeySupplied := by
    intro key declared i mem
    cases declared
    simpa [Key.columns] using mem
  organizationKey := rfl
  checks := [.nonNegative]

private def inputRow (n derived : Int64) : TableRow ValueModel.sqlValue inputSchema :=
  TableRow.ofCells PUnit.unit (fun i => ⟨.integer (if i.val = 0 then n else derived), rfl⟩)

example : (inputSchema.materialize ValueModel.sqlValue sem
    (fun i => (inputRow 7 0).cell i.val)).isSome = true := by decide

example : (CheckedTable.check (sem := sem) [inputRow 7 8]).isSome = true := by decide

example : (CheckedTable.check (sem := sem) [inputRow 7 9]).isNone = true := by decide

example : (CheckedTable.check (sem := sem) [inputRow (-1) 0]).isNone = true := by decide

example : (CheckedTable.check (sem := sem) [inputRow 7 8, inputRow 7 8]).isNone = true := by decide

example : (inputRow 7 8).rowId? = none := rfl

private def parentDb (parent : TableRow ValueModel.sqlValue inputSchema) :
    PackedDatabase ValueModel.sqlValue sem :=
  fun name => if name = "parent" then (CheckedTable.check [parent]).map (fun table => ⟨inputSchema, table⟩) else none

private def references (db : PackedDatabase ValueModel.sqlValue sem) : Bool :=
  let key : ForeignKey inputSchema.Index := ⟨⟨⟨0, by decide⟩, []⟩, "parent", ⟨"input", []⟩⟩
  ((CheckedTable.check (sem := sem) [inputRow 7 8]).map (fun table => key.holds db table)).getD false

example : references (parentDb (inputRow 7 8)) = true := by decide

example : references (parentDb (inputRow 3 4)) = false := by decide

example : inputSchema.resolvesRowId "rowid" = false := rfl

end Silmaril.SQLite.Relational
