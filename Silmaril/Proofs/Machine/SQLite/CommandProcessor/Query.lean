module

public import Silmaril.Logic.RelationalQuery.SQLite.Thms
public import Silmaril.Machine.SQLite.CommandProcessor.Execute.Thms

public section

namespace Silmaril.Machine.SQLite.CommandProcessor.Proofs

open Silmaril.Relational Silmaril.SQLite.Relational
open CatalogExecutor (CatalogPointRead Target queryModelOfSnapshot)

theorem pointRead_sat_iff_execute {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}
    {catalog : TableCatalog Affinity Expr} (read : CatalogPointRead catalog)
    {db : State sem} (compatible : db.catalog.catalog.tables = catalog)
    {vm : VirtualMachine.Database} {locate : Target sem → CodeGenerator.Address}
    {text : String} (parsed : Parser.Represents text ⟨read.table.val, read.columnName⟩)
    (represented : CodeGenerator.Represents vm (locate (read.target db.catalog compatible))
      (read.target db.catalog compatible))
    (key : Int64) (test : SqlValue → Bool) :
    DatabaseQuery.eval (queryModelOfSnapshot db.catalog compatible) (read.sentence key test) = true ↔
      ∃ result after, execute db vm locate text (some (1, key)) = .ok (.statement (.ok result), after) ∧
        result.cell.any test = true := by
  have vmCompatible : CodeGenerator.Compatible db vm locate
      (request db ⟨read.table.val, read.columnName⟩ (some (1, key))) := by
    intro call plan _ classified resolution _
    change CatalogExecutor.classify db.catalog (read.invocation key) = .invoke call at classified
    rw [read.classify_invocation db.catalog compatible key] at classified
    cases classified
    change CatalogExecutor.resolve db.catalog (read.invocation key).statement = .ok plan at resolution
    rw [read.resolve_invocation db.catalog compatible key] at resolution
    cases resolution
    exact represented
  simp only [execute_iff parsed vmCompatible]
  exact read.sat_iff_denote db compatible key test

end Silmaril.Machine.SQLite.CommandProcessor.Proofs
