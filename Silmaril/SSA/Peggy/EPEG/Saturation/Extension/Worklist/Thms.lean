module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Replay

public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist
universe u v

variable {State : Type u} {Action : Type v} {driver : Driver State Action}
variable {source target : State} {fuel : Nat} {report : Report Action}

theorem Driver.check_iff :
    driver.check fuel source report = some target ↔
      driver.replay source report.sites = some target ∧
        report.sites.length ≤ fuel ∧ driver.checkStop fuel target report = true :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist.check_iff driver

theorem Driver.check_fixed (hit : driver.check fuel source report = some target)
    (stop : report.stop = .fixed) : driver.next target = none :=
  Option.isNone_iff_eq_none.mp (by simpa only [Driver.checkStop, stop] using (Driver.check_iff.mp hit).2.2)

theorem Driver.check_exhausted (hit : driver.check fuel source report = some target)
    (stop : report.stop = .exhausted) : report.sites.length = fuel ∧ (driver.next target).isSome = true := by
  have checked := (Driver.check_iff.mp hit).2.2
  simp only [Driver.checkStop, stop, Bool.and_eq_true_iff, decide_eq_true_eq] at checked
  exact checked

theorem Driver.run_checked (enabled : ∀ {s a}, driver.next s = some a → driver.enabled s a = true)
    (fuel : Nat) (s : State) :
    driver.check fuel s (driver.run fuel s).report = some (driver.run fuel s).state :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist.run_checked driver enabled fuel s

theorem Driver.replay_rel (rel : State → State → Prop) (refl : ∀ s, rel s s)
    (trans : ∀ {s t u}, rel s t → rel t u → rel s u)
    (step : ∀ s a, driver.enabled s a = true → rel s (driver.visit s a))
    {sites : List Action} (hit : driver.replay source sites = some target) : rel source target :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist.replay_rel driver rel refl trans step hit

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist
