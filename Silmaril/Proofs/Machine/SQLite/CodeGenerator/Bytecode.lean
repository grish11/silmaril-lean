module

public import Silmaril.Machine.SQLite.CodeGenerator.Bytecode.Defs
import Silmaril.Machine.SQLite.CodeGenerator.Thms
import Silmaril.Machine.SQLite.VirtualMachine.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.CodeGenerator

open Silmaril.Machine.SQLite
open Silmaril.Machine.SQLite.CodeGenerator
open Silmaril.SQLite.Relational
open CatalogExecutor (Names Target profile)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

private theorem transfer_lookup (target : Target sem) (key : Int64)
    {entries : List (Int × List Silmaril.Formats.Sqlite.Value)}
    {rows : List (TableRow ValueModel.sqlValue target.schema)}
    (related : List.Forall₂ (EntryRepresents target) entries rows) :
    Bridge.transferResult (.ok ((Silmaril.Formats.Sqlite.BTree.Abstract.lookupList key.toInt entries).map
        (fun row => row[target.column.val]?.getD .null))) =
      .ok ((rows.find? (fun row => row.rowId? == some key)).map (fun row => row.get target.column)) := by
  induction related with
  | nil => rfl
  | @cons entry row entries rows head _ tail =>
    obtain ⟨⟨id, rowId, vmId⟩, cell, vmCell, transfer⟩ := head
    obtain ⟨number, cells⟩ := entry
    change number = id.toInt at vmId
    change cells[target.column.val]? = some cell at vmCell
    subst number
    by_cases same : id = key
    · subst id
      simp [Silmaril.Formats.Sqlite.BTree.Abstract.lookupList, rowId, vmCell, transfer,
        Bridge.transferResult, Except.map]
    · simpa [Silmaril.Formats.Sqlite.BTree.Abstract.lookupList, Int64.toInt_inj, rowId, same] using tail

theorem run_compile {vm : VirtualMachine.Database} {address : Address} {stmt : Prepared sem}
    (h : stmt.key.isSome → Represents vm address stmt.plan.target) :
    run vm (compile address stmt) =
      .ok ⟨stmt.plan.label, stmt.key.bind stmt.plan.target.lookup⟩ := by
  obtain ⟨plan, key⟩ := stmt
  cases key with
  | none => rfl
  | some key =>
    obtain ⟨table, found, entries⟩ := h rfl
    have vmRun := VirtualMachine.pointProgram_lookup (column := plan.target.column.val) found key
    have projected := transfer_lookup plan.target key entries
    rw [← table.get_eq] at projected
    simp [compile, run, vmRun, projected, CatalogExecutor.Target.lookup, Except.mapError, bind,
      Except.bind, pure, Except.pure]

theorem executeRequest_eq {db : State sem} {vm : VirtualMachine.Database}
    {locate : Target sem → Address} {request : CheckedRequest Names}
    (h : Compatible db vm locate request) :
    executeRequest db vm locate request = .ok ((CatalogExecutor.executor sem).check db request) := by
  cases request with
  | unsupported feature => rfl
  | invoke call =>
    cases resolved : CatalogExecutor.resolve db.catalog call.statement with
    | error error =>
      simp [executeRequest, compileRequest, prepare, Executor.prepare, CatalogExecutor.executor,
        resolved, Except.mapError, bind, Except.bind, CompileError.reply, Executor.check,
        CheckedOutcome.ofStatement, Executor.execute]
    | ok plan =>
      cases binding : call.binding with
      | none =>
        simp [executeRequest, compileRequest, prepare, Executor.prepare, CatalogExecutor.executor,
          resolved, binding, Except.mapError, bind, Except.bind, Executor.check,
          CheckedOutcome.ofStatement, Executor.execute, Executor.run, compile, run, Except.map]
      | some bindCall =>
        obtain ⟨index, key⟩ := bindCall
        by_cases slot : index = 1
        · subst index
          have represented := h call plan key rfl resolved binding
          have vmRun := run_compile
            (stmt := (⟨plan, some key⟩ : Prepared sem)) (fun _ => represented)
          simp [executeRequest, compileRequest, prepare, Executor.prepare, CatalogExecutor.executor,
            resolved, binding, Except.mapError, bind, Except.bind, Executor.check,
            CheckedOutcome.ofStatement, Executor.execute, Executor.run, Prepared.bindInt64, vmRun,
            Except.map, CatalogExecutor.readOutcome, ReadOutcome.finish]
        · simp [executeRequest, compileRequest, prepare, Executor.prepare, CatalogExecutor.executor,
            resolved, binding, Except.mapError, bind, Except.bind, Executor.check,
            CheckedOutcome.ofStatement, Executor.execute, Prepared.bindInt64, slot, CompileError.reply]

end Silmaril.Proofs.Machine.SQLite.CodeGenerator
