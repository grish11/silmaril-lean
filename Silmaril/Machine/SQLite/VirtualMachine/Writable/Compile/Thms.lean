module

public import Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile.Defs
public import Silmaril.Machine.SQLite.VirtualMachine.Writable.Thms
import Silmaril.Proofs.Machine.SQLite.VirtualMachine.Writable.Compile

/-! The compilation relation lands inside the bytecode restriction.

For a footprint `G`, the image of `Compiles` on statements whose source
footprint lies in `G` is contained in the bytecode restricted to `G`, both the
syntactic restriction `within` and the semantic `TargetRestricted`. The
inclusion is one-way and strict (`image_strict`). Scripts compose: the
footprint of a compiled script is the union of its statements' source
footprints, the guard is transparent for it, and tables no statement writes
are unchanged. -/

public section

namespace Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile

open Silmaril.Formats.Sqlite

variable {cat : Catalog}

theorem compiles_within {stmt : Stmt} {code : RawProgram} (h : Compiles cat stmt code) :
    within (Footprint.ofList stmt.footprint) cat code = true :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.Compile.compiles_within h

theorem compiles_within_of {G : Footprint} {stmt : Stmt} {code : RawProgram}
    (h : Compiles cat stmt code) (hG : ∀ touch ∈ stmt.footprint, G.allows touch = true) :
    within G cat code = true :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.Compile.compiles_within_of h hG

/-- One-way image inclusion: compiling a statement that touches only `G`
yields bytecode that, unguarded and with any fallback, touches only `G`. -/
theorem image_targetRestricted {G : Footprint} {code : RawProgram}
    (h : ∃ stmt, (∀ touch ∈ stmt.footprint, G.allows touch = true) ∧ Compiles cat stmt code) :
    TargetRestricted G cat code :=
  let ⟨_, hG, hc⟩ := h
  targetRestricted_of_within (compiles_within_of hc hG)

/-- The guard never refuses compiled code inside its footprint. -/
theorem compiles_run_eq_top {G : Footprint} {stmt : Stmt} {code : RawProgram}
    (h : Compiles cat stmt code) (hG : ∀ touch ∈ stmt.footprint, G.allows touch = true)
    (fuel : Nat) (c : Config) :
    run G cat code fuel c = run Footprint.top cat code fuel c :=
  run_eq_top (compiles_within_of h hG) fuel c

/-- The inclusion is strict: `Halt 0` is restricted to every footprint and is
the image of no statement. -/
theorem image_strict (G : Footprint) :
    TargetRestricted G cat #[Code.halt] ∧ ∀ stmt, ¬ Compiles cat stmt #[Code.halt] :=
  ⟨targetRestricted_of_within (Proofs.Machine.SQLite.VirtualMachine.Writable.Compile.within_halt G),
    Proofs.Machine.SQLite.VirtualMachine.Writable.Compile.not_compiles_halt⟩

theorem target_iff (stmt : Stmt) (table : TableId) :
    Touch.table table .write ∈ stmt.footprint ↔ stmt.target? = some table :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.Compile.target_iff stmt table

theorem scriptFootprint_writes {stmts : List Stmt} {table : TableId} :
    (scriptFootprint stmts).Writes table ↔ ∃ stmt ∈ stmts, stmt.target? = some table :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.Compile.scriptFootprint_writes

/-- Composition over autocommit scripts. Under the union of the source
footprints the guarded script equals the unguarded one, every event is in that
union, and a table that no statement writes keeps its initial contents. -/
theorem compiled_script {stmts : List Stmt} {codes : List RawProgram}
    (h : CompilesScript cat stmts codes) (fuel : Nat) (store : Store) :
    runScript (scriptFootprint stmts) cat fuel codes store =
        runScript Footprint.top cat fuel codes store ∧
      (∀ event ∈ (runScript Footprint.top cat fuel codes store).1,
        event.Allowed (scriptFootprint stmts)) ∧
      Frame (fun table => ∃ stmt ∈ stmts, stmt.target? = some table)
        store (runScript Footprint.top cat fuel codes store).2 :=
  Proofs.Machine.SQLite.VirtualMachine.Writable.Compile.compiled_script h fuel store

end Silmaril.Machine.SQLite.VirtualMachine.Writable.Compile
