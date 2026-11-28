module

public import Silmaril.Machine.SQLite.Interface.Defs
public import Silmaril.Machine.SQLite.CommandProcessor.Execute.Thms
public import Silmaril.Machine.SQLite.BTree.Thms
import Silmaril.Proofs.Machine.SQLite.Interface.Execution

public section

namespace Silmaril.Machine.SQLite.Interface

open Silmaril.SQLite.Relational
open Silmaril.Machine.SqliteVfs (FileState Trace readOnly)
open CatalogExecutor (Target profile)

variable {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}

theorem bindInt64_one (stmt : Prepared sem) (key : Int64) :
    bindInt64 stmt 1 key = (.ok (), ⟨stmt.plan, some key⟩) :=
  ite_eq_left rfl

theorem bindInt64_outOfRange (stmt : Prepared sem) (index : Int32) (key : Int64)
    (outOfRange : index ≠ 1) :
    bindInt64 stmt index key = (.error .range, stmt) :=
  ite_eq_right outOfRange

/-- The compiled VM and D3 prepared execution give the same result and
connection, including the session. Only a bound statement needs a VM table. -/
theorem executePrepared_eq (db : Connection sem) (vm : VirtualMachine.Database)
    (address : CodeGenerator.Address) (stmt : Prepared sem)
    (represented : stmt.key.isSome → CodeGenerator.Represents vm address stmt.plan.target) :
    executePrepared db vm address stmt = .ok ((CatalogExecutor.executor sem).run db stmt) :=
  Proofs.Machine.SQLite.Interface.executePrepared_eq db vm address stmt represented

/-- Successful text preparation and a slot-one bind select the compiled
execution of exactly the resolved D3 plan with that key. -/
theorem prepare_bind_execute (db : Connection sem) (vm : VirtualMachine.Database)
    (address : CodeGenerator.Address) (text : String) (stmt : Prepared sem) (key : Int64)
    (prepared : prepare db text = .ok stmt)
    (represented : CodeGenerator.Represents vm address stmt.plan.target) :
    CommandProcessor.Prepares db text stmt ∧
    bindInt64 stmt 1 key = (.ok (), ⟨stmt.plan, some key⟩) ∧
    executePrepared db vm address (bindInt64 stmt 1 key).2 =
      .ok ((CatalogExecutor.executor sem).run db ⟨stmt.plan, some key⟩) := by
  refine ⟨(CommandProcessor.prepare_iff db text stmt).mp prepared, bindInt64_one stmt key, ?_⟩
  rw [bindInt64_one]
  exact executePrepared_eq db vm address _ (fun _ => represented)

theorem execute_iff {db : Connection sem} {vm : VirtualMachine.Database}
    {address : Target sem → CodeGenerator.Address} {text : String} {stmt : Parser.Statement}
    {binding : Option (Int32 × Int64)} (parsed : Parser.Represents text stmt)
    (compatible : CodeGenerator.Compatible db vm address (CommandProcessor.request db stmt binding))
    (out : CheckedOutcome (profile sem)) :
    execute db vm address text binding = .ok out ↔
      CatalogExecutor.denote sem db (CommandProcessor.invocation stmt binding) out :=
  CommandProcessor.execute_iff parsed compatible out

/-- Use the same designated table in the compiled VM and admitted cold/warm
backend read. The comparison is on the D3 reply after storage erasure. The
D4 batch retains its actual backing, installed slot and single exchange. -/
theorem execute_cold_warm (capacity : Nat) (locate : Bridge.Locate sem)
    (db : Silmaril.SQLite.Relational.Connection (Bridge.profile sem FileState))
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
      Trace.Valid (readOnly capacity) db.backing suffix after.backing :=
  Proofs.Machine.SQLite.Interface.execute_cold_warm capacity locate db vm address text stmt plan
    key table parsed bound leaf projected supplied rows

end Silmaril.Machine.SQLite.Interface
