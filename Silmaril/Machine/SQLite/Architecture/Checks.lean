module

import Silmaril.Machine.SQLite.Architecture.All

/-! Consumer checks through the architecture's public import. -/

namespace Silmaril.Machine.SQLite.Architecture.Checks

open Silmaril.Formats Silmaril.Formats.Sqlite
open Silmaril.SQLite.Relational
open Silmaril.Machine.SqliteVfs (FileState)
open CatalogExecutor (Target profile)

example : Node.interface ∈ nodes := nodes_complete _

example (stmt : Parser.Statement) (wellFormed : stmt.WellFormed) :
    CommandProcessor.parse (Parser.print stmt) = .ok stmt :=
  CommandProcessor.parse_print wellFormed

example (vm : VirtualMachine.Database) (code : VirtualMachine.Program) (fuel : Nat)
    (start : VirtualMachine.State) :
    (VirtualMachine.Traced.runWithTrace vm code fuel start).result =
      VirtualMachine.run vm code fuel start :=
  VirtualMachine.Traced.runWithTrace_result vm code fuel start

example (vm : VirtualMachine.Database) (fuel : Nat) (cfg : VirtualMachine.Mutable.Configuration) :
    (VirtualMachine.Mutable.run vm fuel cfg).result =
      VirtualMachine.run vm cfg.erased fuel cfg.state :=
  (VirtualMachine.Mutable.run_represents vm fuel cfg).1

example : VirtualMachine.Concurrent.simulate .mixed
    (fun (_ : Unit) => ⟨.idle, .plain, false⟩) (fun _ _ _ => none) 0 [] =
    some (some ⟨[], []⟩) := by decide

example {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}
    (db : Interface.Connection sem) (location : CodeGenerator.Address) (plan : Plan (Target sem)) :
    Interface.executePrepared db (fun _ _ => none) location ⟨plan, none⟩ =
      .ok (.ok ⟨plan.label, none⟩, db) := rfl

example {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}
    (db : Interface.Connection sem) (vm : VirtualMachine.Database) (location : CodeGenerator.Address)
    (text : String) (prepared : Interface.Prepared sem) (key : Int64)
    (ready : Interface.prepare db text = .ok prepared)
    (represented : CodeGenerator.Represents vm location prepared.plan.target) :
    Interface.executePrepared db vm location (Interface.bindInt64 prepared 1 key).2 =
      .ok ((CatalogExecutor.executor sem).run db ⟨prepared.plan, some key⟩) :=
  (Interface.prepare_bind_execute db vm location text prepared key ready represented).2.2

example {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}
    (db : Interface.Connection sem) (vm : VirtualMachine.Database)
    (location : Target sem → CodeGenerator.Address) (text : String) (stmt : Parser.Statement)
    (binding : Option (Int32 × Int64)) (out : CheckedOutcome (profile sem))
    (parsed : Parser.Represents text stmt)
    (compatible : CodeGenerator.Compatible db vm location (CommandProcessor.request db stmt binding))
    (denoted : CatalogExecutor.denote sem db (CommandProcessor.invocation stmt binding) out) :
    Interface.execute db vm location text binding = .ok out :=
  (Interface.execute_iff parsed compatible out).mpr denoted

example {Expr : Type} {sem : TableSemantics SqlValue Affinity Expr}
    (capacity : Nat) (locate : Bridge.Locate sem)
    (db : Connection (Bridge.profile sem FileState))
    (vm : VirtualMachine.Database) (address : Target sem → CodeGenerator.Address)
    (text : String) (stmt : Parser.Statement) (plan : Plan (Target sem)) (key : Int64)
    (table : VirtualMachine.Table) (parsed : Parser.Represents text stmt)
    (bound : Bridge.Bound db (CommandProcessor.invocation stmt (some (1, key))) plan key)
    (leaf : Bridge.ColdLeaf db (locate plan.target) table)
    (projected : Bridge.Projected plan.target table key)
    (supplied : vm (address plan.target).database (address plan.target).root = some table)
    (rows : List.Forall₂ (CodeGenerator.EntryRepresents plan.target) table.entries plan.target.table.rows) :
    ∃ cell, Interface.execute (Bridge.forgetStorage db) vm address text (some (1, key)) =
      .ok (.statement (.ok ⟨plan.label, cell⟩), Bridge.forgetStorage db) := by
  obtain ⟨_, cell, execution, _, _⟩ :=
    Interface.execute_cold_warm capacity locate db vm address text stmt plan key table parsed bound
      leaf projected supplied rows
  exact ⟨cell, execution⟩

example (files after : VFS.FileMap) (reason : VFS.OpenError)
    (failure : VFS.openExisting .readWrite 512 true .readOnly "file:sample.db?mode=rw" files =
      (.error reason, after)) : after = files :=
  VFS.open_error_preserves failure

example : ¬ (Pager.LockGrant.mk ⟨"sample.db", ⟨17⟩⟩ .shared).Allows
    ⟨"sample.db", ⟨17⟩⟩ .readWrite := by
  simp [Pager.LockGrant.Allows]

private def codecFixture : TestCode.Fixture File.View (Option (UInt64 × Nat)) :=
  ⟨File.View.ofBytes (Bytes.ofList [129, 0]), some (128, 2)⟩

example : codecFixture.Passes (fun view => Varint.read? view 0) :=
  (TestCode.Fixture.check_iff codecFixture _).mp (by decide)

#print axioms Interface.bindInt64_one
#print axioms Interface.bindInt64_outOfRange
#print axioms Interface.executePrepared_eq
#print axioms Interface.prepare_bind_execute
#print axioms Interface.execute_iff
#print axioms Interface.execute_cold_warm
#print axioms Utilities.varint_roundtrip
#print axioms TestCode.Fixture.check_iff

#print axioms Tokenizer.tokenize_iff
#print axioms Parser.parse_iff
#print axioms CodeGenerator.run_compile
#print axioms CommandProcessor.execute_iff
#print axioms VirtualMachine.pointProgram_lookup
#print axioms VirtualMachine.Traced.wp_snapshots
#print axioms VirtualMachine.Mutable.run_represents
#print axioms VirtualMachine.Concurrent.simulate_ordinary_iff
#print axioms BTree.catalog_cold_warm
#print axioms Pager.commit_reopens
#print axioms Pager.sync_failure_preserves_database
#print axioms VFS.open_success

end Silmaril.Machine.SQLite.Architecture.Checks
