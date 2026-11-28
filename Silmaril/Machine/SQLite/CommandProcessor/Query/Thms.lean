module

public import Silmaril.Logic.RelationalQuery.SQLite.Thms
public import Silmaril.Machine.SQLite.CommandProcessor.Execute.Thms
import Silmaril.Proofs.Machine.SQLite.CommandProcessor.Query

public section

namespace Silmaril.Machine.SQLite.CommandProcessor

open Silmaril.Relational Silmaril.SQLite.Relational
open CatalogExecutor (CatalogPointRead Target queryModelOfSnapshot)

/-- The modeled compiler and VM observe the same projected-cell test as the catalog sentence
when the text represents the declared names and the addressed VM table represents the target. -/
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
        result.cell.any test = true :=
  Proofs.pointRead_sat_iff_execute read compatible parsed represented key test

end Silmaril.Machine.SQLite.CommandProcessor
