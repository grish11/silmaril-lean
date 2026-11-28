module

public import Silmaril.Machine.SQLite.VirtualMachine.Traced.Defs

public section

namespace Silmaril.Proofs.Machine.SQLite.VirtualMachine.Traced

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.VirtualMachine
open Silmaril.Machine.SQLite.VirtualMachine.Traced

theorem runWithTrace_result (db : Database) (code : Program) (fuel : Nat) (start : State) :
    (runWithTrace db code fuel start).result = run db code fuel start := by
  induction fuel generalizing start with
  | zero => by_cases halted : start.halted.isSome <;> simp [runWithTrace, Vdbe.run, halted]
  | succ fuel ih =>
    by_cases halted : start.halted.isSome
    · simp [runWithTrace, Vdbe.run, halted]
    · cases next : step db code start <;>
        simp [runWithTrace, stepWithTrace, Vdbe.run, halted, next, ih]

theorem wp_snapshots {snapshots : Set Database} {code : Program} {fuel : Nat} {start : State}
    {post : Report → Prop} :
    WP (behaviors snapshots code fuel start) post ↔
      snapshots.Nonempty ∧ ∀ db ∈ snapshots,
        (observe (run db code fuel start)).termination = .halted 0 ∧
          post (runWithTrace db code fuel start).report := by
  constructor
  · rintro ⟨⟨_, db, allowed, _⟩, all⟩
    refine ⟨⟨db, allowed⟩, fun candidate h => ?_⟩
    have spec := all _ ⟨candidate, h, rfl⟩
    simpa [Execution.report, runWithTrace_result] using spec
  · rintro ⟨⟨db, allowed⟩, all⟩
    refine ⟨⟨_, db, allowed, rfl⟩, ?_⟩
    rintro _ ⟨candidate, h, rfl⟩
    simpa [Execution.report, runWithTrace_result] using all candidate h

theorem wp_weakest {Input : Type} (runs : Input → Set Report) (pre : Input → Prop)
    (post : Report → Prop) :
    (∀ input, pre input → WP (runs input) post) ↔
      (∀ input, pre input → (runs input).Nonempty) ∧
        ∀ input, pre input → ∀ report ∈ runs input,
          report.observation.termination = .halted 0 ∧ post report := by
  constructor
  · intro h
    exact ⟨fun input p => (h input p).1, fun input p => (h input p).2⟩
  · rintro ⟨enabled, correct⟩ input p
    exact ⟨enabled input p, correct input p⟩

end Silmaril.Proofs.Machine.SQLite.VirtualMachine.Traced
