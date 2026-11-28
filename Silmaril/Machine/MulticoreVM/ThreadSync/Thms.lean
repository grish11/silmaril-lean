module

public import Silmaril.Machine.MulticoreVM.ThreadSync.Defs
public import Silmaril.Machine.MulticoreVM.Thms
import Silmaril.Proofs.Machine.MulticoreVM.ThreadSync.Basic

public section

namespace Silmaril.Machine.MulticoreVM.ThreadSync

open Silmaril.Semantics.ConcurrentTrace (Word)

universe u

variable {Thread Key Value Local Output : Type u}
variable [DecidableEq Thread] [DecidableEq Key] [DecidableEq Value]
variable {cfg final : Config Thread Key Value Local} {thread : Thread} {waiters : List Thread}
variable {program : Program Thread Key Value Local Output}
variable {fragment : Fragment Thread (Event Thread Key Value Output)}

/-- Every successful transition starts from a runnable slot with an available action. -/
theorem step_runnable (h : step program thread waiters cfg fragment final) :
    ∃ localState action,
      cfg.threads thread = some (.runnable localState) ∧ program thread localState = some action :=
  Proofs.Machine.MulticoreVM.ThreadSync.step_runnable h

/-- A wait checks the incoming word and commits the matching park or mismatch continuation. -/
theorem wait_step_iff {key : Key} {expected : Value} {localState onMismatch onWake : Local}
    (ready : cfg.threads thread = some (.runnable localState))
    (action : program thread localState = some (.wait key expected onMismatch onWake)) :
    step program thread waiters cfg fragment final ↔ waiters = [] ∧
      ((cfg.words key = expected ∧ final = cfg.put thread (.parked key onWake) ∧
        fragment = [.event (.waitPark key expected)]) ∨
      (cfg.words key ≠ expected ∧ final = cfg.put thread (.runnable onMismatch) ∧
        fragment = [.event (.waitMismatch key expected (cfg.words key))])) :=
  Proofs.Machine.MulticoreVM.ThreadSync.wait_step_iff ready action

omit [DecidableEq Thread] [DecidableEq Value] in
/-- Every selected thread has a parked continuation at exactly the wake key. -/
theorem wakeAllowed_iff {key : Key} {limit : Nat} :
    WakeAllowed cfg key limit waiters ↔ waiters.length ≤ limit ∧ waiters.Nodup ∧
      ∀ waiter ∈ waiters, ∃ saved, cfg.threads waiter = some (.parked key saved) :=
  Proofs.Machine.MulticoreVM.ThreadSync.wakeAllowed_iff

/-- A successful wake restores precisely the selected waiters, returns their count to the
waker's continuation, and marks the actual participants in its fragment. -/
theorem wake_step_iff {key : Key} {limit : Nat} {localState : Local} {next : Nat → Local}
    (ready : cfg.threads thread = some (.runnable localState))
    (action : program thread localState = some (.wake key limit next)) :
    step program thread waiters cfg fragment final ↔ WakeAllowed cfg key limit waiters ∧
      final = (cfg.resume waiters).put thread (.runnable (next waiters.length)) ∧
      fragment = wakeFragment thread key limit waiters :=
  Proofs.Machine.MulticoreVM.ThreadSync.wake_step_iff ready action

/-- The nondeterministic VM run consists of exactly the successful explicit schedules
of the given length, with their final states and chronological words. -/
theorem mem_run_iff_execute (n : Nat) {word : Word Thread (Event Thread Key Value Output)} :
    (final, word) ∈ namedOutcomes (run (step program) n) cfg ↔
      ∃ schedule : Schedule Thread (List Thread), schedule.length = n ∧
        execute (exec program) schedule cfg = some (final, word) := by
  rw [mem_run_iff_exists_schedule]
  simp only [execute_iff_scheduled]

end Silmaril.Machine.MulticoreVM.ThreadSync
