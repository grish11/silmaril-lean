module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Defs

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist
universe u v

open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist

variable {State : Type u} {Action : Type v} (driver : Driver State Action)
variable {source target : State}

theorem check_iff {fuel : Nat} {report : Report Action} :
    driver.check fuel source report = some target ↔
      driver.replay source report.sites = some target ∧
        report.sites.length ≤ fuel ∧ driver.checkStop fuel target report = true := by
  by_cases budget : report.sites.length ≤ fuel
  · unfold Driver.check
    rw [ite_eq_left budget]
    simp only [budget, true_and]
    cases driver.replay source report.sites with
    | none => simp
    | some reached =>
      by_cases ok : driver.checkStop fuel reached report = true
      · simp only [ite_eq_left ok, Option.some.injEq]
        exact ⟨fun h => ⟨h, h ▸ ok⟩, And.left⟩
      · simp only [ite_eq_right ok, reduceCtorEq, Option.some.injEq, false_iff]
        rintro ⟨rfl, bad⟩
        exact ok bad
  · simp [Driver.check, budget]

private theorem checkStop_cons (fuel : Nat) (state : State)
    (action : Action) (report : Report Action) :
    driver.checkStop (fuel + 1) state ⟨action :: report.sites, report.stop⟩ =
      driver.checkStop fuel state report := by
  obtain ⟨sites, stop⟩ := report
  cases stop <;> simp [Driver.checkStop]

theorem run_checked
    (enabled : ∀ {s a}, driver.next s = some a → driver.enabled s a = true)
    (fuel : Nat) (s : State) :
    driver.check fuel s (driver.run fuel s).report = some (driver.run fuel s).state := by
  induction fuel generalizing s with
  | zero =>
    rw [Driver.run]
    cases pick : driver.next s <;> simp [pick, Driver.check, Driver.replay, Driver.checkStop]
  | succ fuel ih =>
    rw [Driver.run]
    cases pick : driver.next s with
    | none => simp [pick, Driver.check, Driver.replay, Driver.checkStop]
    | some i =>
      have hit := enabled pick
      let rest := driver.run fuel (driver.visit s i)
      have accepted : driver.check fuel (driver.visit s i) rest.report = some rest.state :=
        ih (driver.visit s i)
      obtain ⟨trace, budget, verified⟩ := (check_iff driver).mp accepted
      change driver.check (fuel + 1) s ⟨i :: rest.report.sites, rest.report.stop⟩ = some rest.state
      apply (check_iff driver).mpr
      refine ⟨?_, Nat.succ_le_succ budget, (checkStop_cons driver fuel rest.state i rest.report).trans verified⟩
      simpa only [Driver.replay, ite_eq_left hit] using trace

theorem replay_rel (rel : State → State → Prop) (refl : ∀ s, rel s s)
    (trans : ∀ {s t u}, rel s t → rel t u → rel s u)
    (step : ∀ s a, driver.enabled s a = true → rel s (driver.visit s a))
    {sites : List Action} (hit : driver.replay source sites = some target) : rel source target := by
  induction sites generalizing source with
  | nil => cases hit; exact refl _
  | cons action rest ih =>
    unfold Driver.replay at hit
    split at hit
    · rename_i enabled
      exact trans (step source action enabled) (ih hit)
    · cases hit

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist
