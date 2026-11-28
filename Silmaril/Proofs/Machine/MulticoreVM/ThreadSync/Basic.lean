module

public import Silmaril.Machine.MulticoreVM.ThreadSync.Defs
public import Silmaril.Machine.MulticoreVM.Thms

public section

namespace Silmaril.Proofs.Machine.MulticoreVM.ThreadSync

open Silmaril.Machine.MulticoreVM
open Silmaril.Machine.MulticoreVM.ThreadSync
open Silmaril.Semantics.ConcurrentTrace (Word)

universe u

variable {Thread Key Value Local Output : Type u}
variable [DecidableEq Thread] [DecidableEq Key] [DecidableEq Value]
variable {cfg final : Config Thread Key Value Local} {thread : Thread} {waiters : List Thread}
variable {program : Program Thread Key Value Local Output}
variable {fragment : Fragment Thread (Event Thread Key Value Output)}

theorem step_runnable (h : step program thread waiters cfg fragment final) :
    ∃ localState action,
      cfg.threads thread = some (.runnable localState) ∧ program thread localState = some action := by
  change exec program thread waiters cfg = some (final, fragment) at h
  cases hSlot : cfg.threads thread with
  | none => simp [exec, hSlot] at h
  | some slot =>
    cases slot with
    | parked key saved => simp [exec, hSlot] at h
    | runnable localState =>
      cases hAction : program thread localState with
      | none => simp [exec, hSlot, hAction] at h
      | some action => exact ⟨localState, action, rfl, hAction⟩

theorem wait_step_iff {key : Key} {expected : Value} {localState onMismatch onWake : Local}
    (ready : cfg.threads thread = some (.runnable localState))
    (action : program thread localState = some (.wait key expected onMismatch onWake)) :
    step program thread waiters cfg fragment final ↔ waiters = [] ∧
      ((cfg.words key = expected ∧ final = cfg.put thread (.parked key onWake) ∧
        fragment = [.event (.waitPark key expected)]) ∨
      (cfg.words key ≠ expected ∧ final = cfg.put thread (.runnable onMismatch) ∧
        fragment = [.event (.waitMismatch key expected (cfg.words key))])) := by
  change exec program thread waiters cfg = some (final, fragment) ↔ _
  cases waiters <;> by_cases h : cfg.words key = expected <;>
    simp [exec, ready, action, h] <;> simp [eq_comm]

omit [DecidableEq Thread] [DecidableEq Value] in
theorem wakeAllowed_iff {key : Key} {limit : Nat} :
    WakeAllowed cfg key limit waiters ↔ waiters.length ≤ limit ∧ waiters.Nodup ∧
      ∀ waiter ∈ waiters, ∃ saved, cfg.threads waiter = some (.parked key saved) := by
  have parked (waiter : Thread) :
      cfg.parkedAt key waiter = true ↔
        ∃ saved, cfg.threads waiter = some (.parked key saved) := by
    unfold Config.parkedAt
    cases cfg.threads waiter with
    | none => simp
    | some slot => cases slot <;> simp
  simp only [WakeAllowed, List.all_eq_true, parked]

theorem wake_step_iff {key : Key} {limit : Nat} {localState : Local} {next : Nat → Local}
    (ready : cfg.threads thread = some (.runnable localState))
    (action : program thread localState = some (.wake key limit next)) :
    step program thread waiters cfg fragment final ↔ WakeAllowed cfg key limit waiters ∧
      final = (cfg.resume waiters).put thread (.runnable (next waiters.length)) ∧
      fragment = wakeFragment thread key limit waiters := by
  change exec program thread waiters cfg = some (final, fragment) ↔ _
  by_cases allowed : WakeAllowed cfg key limit waiters <;>
    simp [exec, ready, action, allowed, eq_comm]

end Silmaril.Proofs.Machine.MulticoreVM.ThreadSync
