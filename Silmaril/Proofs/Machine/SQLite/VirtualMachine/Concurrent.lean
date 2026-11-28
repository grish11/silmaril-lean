module

public import Silmaril.Machine.SQLite.VirtualMachine.Concurrent.Defs
import Silmaril.Semantics.TrackA.Concurrency.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.VirtualMachine.Concurrent

open Silmaril.Machine.SQLite.VirtualMachine
open Silmaril.Machine.SQLite.VirtualMachine.Concurrent
open Silmaril.Semantics.TrackA
open Silmaril.Semantics.TrackA.Interaction

variable {Thread : Type} [DecidableEq Thread]
variable {profile : Concurrency.RaceProfile} {clients : Thread → Client}
variable {versions : Nat → Database} {generation : Nat}

theorem simulate_ordinary_iff {observed : Report Thread} :
    some observed ∈ explicit profile clients versions generation ↔
      ∃ schedule, simulate profile clients versions generation schedule = some (some observed) := by
  constructor
  · rintro ⟨history, finish, guarded, rfl⟩
    obtain ⟨run, clean⟩ := Concurrency.guarded_iff.mp guarded
    have replayed : Concurrency.replay (initialConfig clients generation)
        (history.map Concurrency.Event.thread) = some (history, finish) :=
      Concurrency.replay_iff.mpr ⟨run, rfl⟩
    exact ⟨history.map Concurrency.Event.thread, by simp [simulate, replayed, clean]⟩
  · rintro ⟨schedule, simulated⟩
    cases replayed : Concurrency.replay (initialConfig clients generation) schedule with
    | none => simp [simulate, replayed] at simulated
    | some raw =>
      obtain ⟨history, finish⟩ := raw
      by_cases race : Concurrency.hasRace profile history
      · simp [simulate, replayed, race] at simulated
      · have clean := Bool.eq_false_iff.mpr race
        have ordinary := (Concurrency.replay_iff.mp replayed).1
        refine ⟨history, finish, Concurrency.guarded_iff.mpr ⟨ordinary, clean⟩, ?_⟩
        simpa [simulate, replayed, clean] using simulated

theorem simulate_ub_iff :
    none ∈ explicit profile clients versions generation ↔
      ∃ schedule, simulate profile clients versions generation schedule = some none := by
  constructor
  · rintro ⟨history, ub⟩
    obtain ⟨finish, run, classified⟩ := Concurrency.raceUB_has_raw_run ub
    have replayed : Concurrency.replay (initialConfig clients generation)
        (history.map Concurrency.Event.thread) = some (history, finish) :=
      Concurrency.replay_iff.mpr ⟨run, rfl⟩
    have race : Concurrency.hasRace profile history = true := by
      simpa [Concurrency.classify] using classified
    exact ⟨history.map Concurrency.Event.thread, by simp [simulate, replayed, race]⟩
  · rintro ⟨schedule, simulated⟩
    cases replayed : Concurrency.replay (initialConfig clients generation) schedule with
    | none => simp [simulate, replayed] at simulated
    | some raw =>
      obtain ⟨history, finish⟩ := raw
      by_cases race : Concurrency.hasRace profile history
      · obtain ⟨firstRace, _, _, ub⟩ :=
          Concurrency.racy_run_has_ub_prefix (Concurrency.replay_iff.mp replayed).1 race
        exact ⟨firstRace, ub⟩
      · simp [simulate, replayed, Bool.eq_false_iff.mpr race] at simulated

end Silmaril.Proofs.Machine.SQLite.VirtualMachine.Concurrent
