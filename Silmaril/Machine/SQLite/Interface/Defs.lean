module

public import Silmaril.Machine.SQLite.CommandProcessor.Execute.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.Interface

open Silmaril.SQLite.Relational
open CatalogExecutor (Target profile)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

/-- The existing D3 connection and its read-only session observation. -/
abbrev Connection (sem : TableSemantics SqlValue Affinity Expr) := CommandProcessor.State sem
abbrev Session := Silmaril.SQLite.Relational.Session

/-- The resolved D3 point plan, including its current one-slot binding. -/
abbrev Prepared (sem : TableSemantics SqlValue Affinity Expr) := CodeGenerator.Prepared sem

abbrev prepare (db : Connection sem) (text : String) :
    Except CommandProcessor.PrepareError (Prepared sem) :=
  CommandProcessor.prepare db text

abbrev bindInt64 (stmt : Prepared sem) (index : Int32) (key : Int64) :
    Except BindError Unit × Prepared sem :=
  stmt.bindInt64 index key

/-- Run a prepared query to completion in the supplied VM snapshot. Use the
connection it was prepared for. A successful VM evaluation returns the
original D3 connection alongside the result. -/
def executePrepared (db : Connection sem) (vm : VirtualMachine.Database)
    (address : CodeGenerator.Address) (stmt : Prepared sem) :
    Except CodeGenerator.RunError (Outcome (profile sem)) :=
  (CodeGenerator.run vm (CodeGenerator.compile address stmt)).map fun result => (.ok result, db)

/-- Perform one complete text invocation. Its ordinary SQL replies carry the
D3 connection. Text rejection and VM/transfer failures use the outer error. -/
abbrev execute (db : Connection sem) (vm : VirtualMachine.Database)
    (address : Target sem → CodeGenerator.Address) (text : String)
    (binding : Option (Int32 × Int64)) :
    Except CommandProcessor.ExecuteError (CheckedOutcome (profile sem)) :=
  CommandProcessor.execute db vm address text binding

end Silmaril.Machine.SQLite.Interface
