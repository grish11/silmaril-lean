module

public import Silmaril.Machine.SQLite.CommandProcessor.Defs
public import Silmaril.Machine.SQLite.CodeGenerator.Bytecode.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.CommandProcessor

open Silmaril.SQLite.Relational
open CatalogExecutor (Target profile)

inductive ExecuteError where
  | text (error : TextError)
  | run (error : CodeGenerator.RunError)
  deriving DecidableEq

/-- A fresh text invocation, with the same prepare and bind ordering as D3. -/
def execute {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}
    (db : State sem) (vm : VirtualMachine.Database) (locate : Target sem → CodeGenerator.Address)
    (text : String) (binding : Option (Int32 × Int64)) :
    Except ExecuteError (CheckedOutcome (profile sem)) := do
  let statement ← (parse text).mapError .text
  (CodeGenerator.executeRequest db vm locate (request db statement binding)).mapError .run

end Silmaril.Machine.SQLite.CommandProcessor
