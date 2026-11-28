module

import Silmaril.Machine.SQLite.CommandProcessor.Query.Thms

namespace Silmaril.Machine.SQLite.CommandProcessor.ExecuteChecks

open Silmaril.Relational Silmaril.SQLite.Relational

private def semantics : TableSemantics SqlValue Affinity Unit where
  evalGenerated _ _ := none
  evalCheck _ _ := none
  keyEqual _ _ a b := decide (a = b)
  foreignEqual _ _ a b := decide (a = b)

private def schema : TableSchema Affinity Unit where
  mode := .dynamic
  width := 2
  column i := ⟨if i.val = 0 then "ignored" else "value", .dynamic none .blob, none, false⟩
  uniqueNames := by
    intro i j h
    have hi : i.val = 0 ∨ i.val = 1 := by omega
    have hj : j.val = 0 ∨ j.val = 1 := by omega
    apply Fin.ext
    rcases hi with hi | hi <;> rcases hj with hj | hj <;> simp_all
  organization := .rowid none
  generation _ := none
  suppliedExists := ⟨0, rfl⟩
  inputsSupplied := by simp
  primaryKeySupplied := by simp
  organizationKey := trivial

private def row (key : Int64) (value : SqlValue) : TableRow ValueModel.sqlValue schema :=
  TableRow.ofCells key (fun i => ⟨if i.val = 0 then .integer 7 else value, rfl⟩)

private def rows : List (TableRow ValueModel.sqlValue schema) :=
  [row (-7) .null, row 9 (.integer 42)]

private def checked : CheckedTable ValueModel.sqlValue semantics schema :=
  (CheckedTable.check rows).get (by decide)

private def connection : State semantics where
  catalog := {
    tables := fun name => if name = "items" then some ⟨schema, checked⟩ else none
    objects := {
      views := fun name => if name = "v" then some ⟨["value"], ()⟩ else none } }
  backing := ()
  cache := ()
  session := ⟨false, 2, 3, -4⟩

private def statement : Parser.Statement := ⟨"items", "value"⟩
private def sql := "SELECT VALUE FROM items WHERE rowid=?1;"
private def address : CodeGenerator.Address := ⟨0, 2⟩
private def locate (_ : CatalogExecutor.Target semantics) : CodeGenerator.Address := address
private def snapshot (table : VirtualMachine.Table) : VirtualMachine.Database :=
  fun database root => if database = 0 ∧ root = 2 then some table else none

private def table : VirtualMachine.Table :=
  Silmaril.Formats.Sqlite.BTree.Query.ReadModel.ofList
    [(-7, [.integer 7, .null]), (9, [.integer 7, .integer 42])]

private def shortTable : VirtualMachine.Table :=
  Silmaril.Formats.Sqlite.BTree.Query.ReadModel.ofList [(-7, [.integer 7]), (9, [.integer 7])]

private def plan : Plan (CatalogExecutor.Target semantics) :=
  ⟨⟨schema, ⟨1, by decide⟩, checked⟩, "value"⟩

private theorem represented : CodeGenerator.Represents (snapshot table) address plan.target := by
  refine ⟨table, rfl, .cons ?_ (.cons ?_ .nil)⟩
  · exact ⟨⟨-7, rfl, rfl⟩, .null, rfl, rfl⟩
  · exact ⟨⟨9, rfl, rfl⟩, .integer 42, rfl, rfl⟩

private theorem compatible (binding : Option (Int32 × Int64)) :
    CodeGenerator.Compatible connection (snapshot table) locate (request connection statement binding) := by
  intro call resolved key classified resolution bound
  change CheckedRequest.invoke (invocation statement binding) = .invoke call at classified
  cases classified
  change CatalogExecutor.resolve connection.catalog (invocation statement binding).statement =
    .ok resolved at resolution
  have equal : plan = resolved := Except.ok.inj resolution
  subst resolved
  exact represented

example (binding : Option (Int32 × Int64)) :
    execute connection (snapshot table) locate sql binding =
      .ok (CatalogExecutor.execute semantics connection (invocation statement binding)) :=
  execute_eq ((parse_iff _ _).1 (by cbv)) (compatible binding)

private def observe (vm : VirtualMachine.Database) (text : String) (binding : Option (Int32 × Int64)) :
    Except ExecuteError (CheckedReply (CatalogExecutor.profile semantics)) :=
  (execute connection vm locate text binding).map Prod.fst

example : observe (snapshot table) sql (some (1, -7)) =
    .ok (.statement (.ok ⟨"value", some .null⟩)) := by cbv

example : observe (snapshot table) sql (some (1, 9)) =
    .ok (.statement (.ok ⟨"value", some (.integer 42)⟩)) := by cbv

example : observe (snapshot table) sql (some (1, 8)) =
    .ok (.statement (.ok ⟨"value", none⟩)) := by cbv

example : observe (fun _ _ => none) sql none = .ok (.statement (.ok ⟨"value", none⟩)) := by cbv

example : observe (fun _ _ => none) sql (some (2, 9)) =
    .ok (.statement (.error (.bind .range))) := by cbv

example : observe (fun _ _ => none) "SELECT absent FROM items WHERE rowid=?1" (some (2, 9)) =
    .ok (.statement (.error (.prepare (.missingColumn "items" "absent")))) := by cbv

example : observe (fun _ _ => none) "SELECT value FROM v WHERE rowid=?1" (some (2, 9)) =
    .ok (.unsupported "view") := by cbv

example : observe (fun _ _ => none) "SELECT value FROM items WHERE value=?1" (some (1, 9)) =
    .error (.text .outsideGrammar) := by cbv

example : observe (fun _ _ => none) sql (some (1, 9)) =
    .error (.run (.machine (.termination (.fault (.missingTable 0 2))))) := by cbv

/-- The short snapshot fails representation and its default NULL differs from
the D3 value at rowid nine. -/
example : ¬ CodeGenerator.Represents (snapshot shortTable) address plan.target := by
  rintro ⟨actual, found, paired⟩
  have same : shortTable = actual := Option.some.inj found
  subst actual
  cases paired with
  | cons first rest =>
    obtain ⟨_, cell, bad, _⟩ := first
    change none = some cell at bad
    exact Option.some_ne_none cell bad.symm

example : observe (snapshot shortTable) sql (some (1, 9)) =
    .ok (.statement (.ok ⟨"value", some .null⟩)) := by cbv

private def catalogRead : CatalogExecutor.CatalogPointRead connection.catalog.catalog.tables where
  table := ⟨"items", by decide⟩
  columnName := "value"
  column := ⟨1, by decide⟩
  found := rfl
  rowIdVisible := rfl
  ordinary := rfl

example : DatabaseQuery.eval (CatalogExecutor.queryModelOfSnapshot connection.catalog rfl)
    (catalogRead.sentence (-7) fun value => decide (value = .null)) = true := by
  apply (pointRead_sat_iff_execute (db := connection) (vm := snapshot table) (locate := locate)
    catalogRead rfl ((parse_iff sql statement).mp (by cbv)) represented _ _).mpr
  exact ⟨⟨"value", some .null⟩, connection, by cbv, rfl⟩

end Silmaril.Machine.SQLite.CommandProcessor.ExecuteChecks
