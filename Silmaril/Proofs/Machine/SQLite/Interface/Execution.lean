module

public import Silmaril.Machine.SQLite.Interface.Defs
public import Silmaril.Machine.SQLite.CommandProcessor.Execute.Thms
public import Silmaril.Machine.SQLite.BTree.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.Interface

open Silmaril.Machine.SQLite
open Silmaril.Machine.SQLite.Interface (executePrepared execute)
open Silmaril.SQLite.Relational
open Silmaril.Machine.SqliteVfs (FileState Trace readOnly)
open CatalogExecutor (Target)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

theorem executePrepared_eq (db : Interface.Connection sem) (vm : VirtualMachine.Database)
    (address : CodeGenerator.Address) (stmt : Interface.Prepared sem)
    (represented : stmt.key.isSome → CodeGenerator.Represents vm address stmt.plan.target) :
    executePrepared db vm address stmt = .ok ((CatalogExecutor.executor sem).run db stmt) := by
  unfold executePrepared
  rw [CodeGenerator.run_compile represented]
  rcases db with ⟨catalog, ⟨⟩, ⟨⟩, exchanges, session⟩
  rcases stmt with ⟨plan, key⟩
  cases key with
  | none => rfl
  | some key =>
    simp [Executor.run, CatalogExecutor.executor, CatalogExecutor.readOutcome, ReadOutcome.finish,
      Except.map]

theorem execute_cold_warm (capacity : Nat) (locate : Bridge.Locate sem)
    (db : Connection (Bridge.profile sem FileState))
    (vm : VirtualMachine.Database) (address : Target sem → CodeGenerator.Address)
    (text : String) (stmt : Parser.Statement) (plan : Plan (Target sem)) (key : Int64)
    (table : VirtualMachine.Table) (parsed : Parser.Represents text stmt)
    (bound : Bridge.Bound db (CommandProcessor.invocation stmt (some (1, key))) plan key)
    (leaf : Bridge.ColdLeaf db (locate plan.target) table)
    (projected : Bridge.Projected plan.target table key)
    (supplied : vm (address plan.target).database (address plan.target).root = some table)
    (rows : List.Forall₂ (CodeGenerator.EntryRepresents plan.target) table.entries plan.target.table.rows) :
    ∃ bytes cell,
      let request := locate plan.target
      let call := CommandProcessor.invocation stmt (some (1, key))
      let result : SelectResult SqlValue := ⟨plan.label, cell⟩
      let suffix : Trace := [⟨request.page.request, .ok bytes⟩]
      let after := { db with
        cache := db.cache.install request.target request.page bytes
        exchanges := db.exchanges ++ suffix }
      execute (Bridge.forgetStorage db) vm address text (some (1, key)) =
        .ok (.statement (.ok result), Bridge.forgetStorage after) ∧
      (Bridge.executor (readOnly capacity) locate).executeBatch db [call, call] =
        (⟨[(result, after), (result, after)], none⟩, after) ∧
      Trace.Valid (readOnly capacity) db.backing suffix after.backing := by
  let call := CommandProcessor.invocation stmt (some (1, key))
  have compatible :
      CodeGenerator.Compatible (Bridge.forgetStorage db) vm address
        (CommandProcessor.request (Bridge.forgetStorage db) stmt (some (1, key))) := by
    intro selected resolved _ admitted result _
    have sameCall : call = selected := CheckedRequest.invoke.inj (bound.admitted.symm.trans admitted)
    subst selected
    change CatalogExecutor.resolve db.catalog call.statement = .ok resolved at result
    have samePlan : plan = resolved := Except.ok.inj (bound.resolved.symm.trans result)
    subst resolved
    exact ⟨table, supplied, rows⟩
  obtain ⟨bytes, _, cell, _, _, _, _, _, valid, _, catalog, batch⟩ :=
    BTree.catalog_cold_warm capacity locate db call plan key table bound leaf projected
  exact ⟨bytes, cell, (CommandProcessor.execute_eq parsed compatible).trans (congrArg Except.ok catalog),
    batch, valid⟩

end Silmaril.Proofs.Machine.SQLite.Interface
