module

public import Silmaril.Machine.SQLite.CodeGenerator.Defs
public import Silmaril.Machine.SQLite.VirtualMachine.Defs
public import Silmaril.Machine.SQLite.Relational.Bridge.Defs
public import Batteries.Data.List.Basic

@[expose] public section

namespace Silmaril.Machine.SQLite.CodeGenerator

open Silmaril.SQLite.Relational
open CatalogExecutor (Names Target profile)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

/-- Location supplied by the caller in the VM snapshot. The numbers are VM
operands. This compiler does not allocate or discover database roots. -/
structure Address where
  database : Nat
  root : Nat

/-- An unset parameter short-circuits in D3. A bound point emits the VM's
six-instruction template and retains the D3 projection label. -/
inductive Compiled where
  | unbound (label : String)
  | point (label : String) (program : VirtualMachine.Program)

def compile (address : Address) (stmt : Prepared sem) : Compiled :=
  match stmt.key with
  | none => .unbound stmt.plan.label
  | some key => .point stmt.plan.label
      (VirtualMachine.pointProgram address.database address.root stmt.plan.target.column.val key)

inductive RunError where
  | machine (error : VirtualMachine.PointError)
  | transfer (error : Bridge.ReadFailure)
  deriving DecidableEq

/-- Observe a point at a budget of six VM steps, using D4's existing value
transfer. A missing row is retained separately from a present SQL NULL. -/
def run (vm : VirtualMachine.Database) : Compiled → Except RunError (SelectResult SqlValue)
  | .unbound label => .ok ⟨label, none⟩
  | .point label program => do
    let observed := VirtualMachine.observe (VirtualMachine.run vm program 6 VirtualMachine.initial)
    let cell ← (VirtualMachine.pointResult observed).mapError .machine
    let value ← (Bridge.transferResult (.ok cell)).mapError .transfer
    return ⟨label, value⟩

/-- Compare the signed rowid and the selected column. The column must exist in
the VM row, so the VM's default NULL for a short row cannot witness this relation. -/
def EntryRepresents (target : Target sem) (entry : Int × List Silmaril.Formats.Sqlite.Value)
    (row : TableRow ValueModel.sqlValue target.schema) : Prop :=
  (∃ key : Int64, row.rowId? = some key ∧ entry.1 = key.toInt) ∧
  ∃ cell, entry.2[target.column.val]? = some cell ∧
    Bridge.transferCell cell = .ok (row.get target.column)

/-- The supplied location contains a VM table whose entries pair with the
checked D3 rows in order. Only rowids and the selected cells are observed. -/
def Represents (vm : VirtualMachine.Database) (address : Address) (target : Target sem) : Prop :=
  ∃ table, vm address.database address.root = some table ∧
    List.Forall₂ (EntryRepresents target) table.entries target.table.rows

inductive CompileError where
  | prepare (error : PrepareError)
  | bind (error : BindError)
  deriving DecidableEq, Repr

def CompileError.reply (error : CompileError) : CheckedReply (profile sem) :=
  match error with
  | .prepare (.unsupported feature) => .unsupported feature
  | .prepare (.resolve error) => .statement (.error (.prepare error))
  | .bind error => .statement (.error (.bind error))

/-- Compile one already classified D3 call, reusing the planner and the D3
one-slot bind operation. Prepare failure precedes examination of the binding. -/
def compileRequest (db : State sem) (locate : Target sem → Address) :
    CheckedRequest Names → Except CompileError Compiled
  | .unsupported feature => .error (.prepare (.unsupported feature))
  | .invoke call => do
    let stmt ← (prepare db (.invoke call)).mapError .prepare
    match call.binding with
    | none => .ok (compile (locate stmt.plan.target) stmt)
    | some (index, key) =>
      match stmt.bindInt64 index key with
      | (.error error, _) => .error (.bind error)
      | (.ok (), bound) => .ok (compile (locate bound.plan.target) bound)

/-- Preserve the D3 connection on every D3 reply. VM and transfer failures
describe failures of the supplied machine path in a separate result channel. -/
def executeRequest (db : State sem) (vm : VirtualMachine.Database) (locate : Target sem → Address)
    (request : CheckedRequest Names) : Except RunError (CheckedOutcome (profile sem)) :=
  match compileRequest db locate request with
  | .error error => .ok (error.reply, db)
  | .ok compiled => (run vm compiled).map fun result => (.statement (.ok result), db)

/-- A represented VM table is required only when an admitted, resolved call
has a binding to slot one. These are exactly the calls that access the VM. -/
def Compatible (db : State sem) (vm : VirtualMachine.Database) (locate : Target sem → Address)
    (request : CheckedRequest Names) : Prop :=
  ∀ call plan key, request = .invoke call →
    (CatalogExecutor.reference sem).resolves db.catalog call.statement (.ok plan) →
    call.binding = some (1, key) → Represents vm (locate plan.target) plan.target

end Silmaril.Machine.SQLite.CodeGenerator
