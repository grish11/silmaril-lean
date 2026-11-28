module

public import Silmaril.Machine.SQLite.VirtualMachine.Mutable.Defs

public section

namespace Silmaril.Proofs.Machine.SQLite.VirtualMachine.Mutable

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine
open Silmaril.Machine.SQLite.VirtualMachine.Mutable

private theorem erase_cache (cell : Cell) : cell.cache.erase = cell.erase := by
  cases cell with
  | original instruction => cases instruction <;> rfl
  | cachedString => rfl

theorem ofProgram_represents (code : Program) (state : State) :
    Represents (Configuration.ofProgram code state) code state := by
  constructor
  · simp [Configuration.ofProgram, Configuration.erased, Array.map_map, Function.comp_def, Cell.erase]
  · rfl

theorem step_state (db : Database) (cfg : Configuration) :
    (Mutable.step db cfg).map Configuration.state =
      Vdbe.step db cfg.erased cfg.state := by
  by_cases halted : cfg.state.halted.isSome
  · simp [Mutable.step, Vdbe.step, halted, Except.map]
  · cases fetched : cfg.code[cfg.state.pc]? with
    | none => simp [Mutable.step, Vdbe.step, Configuration.erased, halted, fetched, Except.map]
    | some cell =>
        cases executed : Vdbe.execute db cell.erase cfg.state <;>
          simp [Mutable.step, Vdbe.step, Configuration.erased, halted, fetched, executed, Except.map]

theorem step_erased {db : Database} {before after : Configuration}
    (stepped : Mutable.step db before = .ok after) : after.erased = before.erased := by
  by_cases halted : before.state.halted.isSome
  · simp [Mutable.step, halted] at stepped
  · cases fetched : before.code[before.state.pc]? with
    | none => simp [Mutable.step, halted, fetched] at stepped
    | some cell =>
        cases executed : Vdbe.execute db cell.erase before.state with
        | error => simp [Mutable.step, halted, fetched, executed, Except.map] at stepped
        | ok s =>
          have afterCode : after.code = before.code.setIfInBounds before.state.pc cell.cache := by
            simp [Mutable.step, halted, fetched, executed, Except.map] at stepped
            exact congrArg Configuration.code stepped.symm
          rw [Configuration.erased, afterCode, Array.map_setIfInBounds, erase_cache]
          apply Array.ext_getElem?
          intro index
          by_cases same : before.state.pc = index
          · subst index
            obtain ⟨inBounds, atIndex⟩ := Array.getElem?_eq_some_iff.mp fetched
            simp [inBounds, atIndex, Configuration.erased]
          · simp [same, Configuration.erased]

theorem run_represents (db : Database) (fuel : Nat) (cfg : Configuration) :
    (Mutable.run db fuel cfg).result = Vdbe.run db cfg.erased fuel cfg.state ∧
      (Mutable.run db fuel cfg).code.map Cell.erase = cfg.erased := by
  induction fuel generalizing cfg with
  | zero =>
    by_cases halted : cfg.state.halted.isSome <;>
      simp [Mutable.run, Vdbe.run, halted, Configuration.erased]
  | succ fuel ih =>
    by_cases halted : cfg.state.halted.isSome
    · simp [Mutable.run, Vdbe.run, halted, Configuration.erased]
    · have core := step_state db cfg
      cases stepped : Mutable.step db cfg with
      | error fault =>
        simp [stepped, Except.map] at core
        exact ⟨by simp [Mutable.run, Vdbe.run, halted, stepped, ← core],
          by simp [Mutable.run, halted, stepped, Configuration.erased]⟩
      | ok after =>
        simp [stepped, Except.map] at core
        have erased := step_erased stepped
        constructor
        · calc
            (Mutable.run db (fuel + 1) cfg).result = Vdbe.run db after.erased fuel after.state := by
              simpa [Mutable.run, halted, stepped] using (ih after).1
            _ = Vdbe.run db cfg.erased (fuel + 1) cfg.state := by
              rw [erased]
              simp [Vdbe.run, halted, ← core]
        · simpa [Mutable.run, halted, stepped, erased] using (ih after).2

end Silmaril.Proofs.Machine.SQLite.VirtualMachine.Mutable
