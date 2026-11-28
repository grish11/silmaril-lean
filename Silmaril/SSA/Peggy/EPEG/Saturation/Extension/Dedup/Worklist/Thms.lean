module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Search
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Replay
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Thms

public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist

open PEG
open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {l : Nat}
variable {zero : P [] .count} {source target : Output P params results l}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}
variable [DecidableEq Data] [DecidableEq (P [] .count)]

theorem enabled_spec (s : Output P params results l) (i : Fin s.1) :
    enabled zero s i = true ↔ ∃ found : ZeroSample s.2.graph i zero, ¬ Covered found s.2.classes :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.enabled_iff s i

theorem checkFixed_iff (s : Output P params results l) : checkFixed zero s = true ↔ Fixed zero s :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.closed_iff s

theorem fixed_stutters (s : Output P params results l) (address : Nat)
    (closed : Fixed zero s) : visit zero s address = s :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.fixed_visit s address closed

theorem check_replay {fuel : Nat} {report : Report} :
    check zero fuel source report = some target ↔
      replay zero source report.sites = some target ∧
        report.sites.length ≤ fuel ∧ checkStop zero fuel target report = true :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.check_iff

/-- The producer's receipt checks against the original input. The checker
recomputes the endpoint and verifies its stop claim. -/
theorem run_checked (fuel : Nat) (s : Output P params results l) :
    check zero fuel s (run zero fuel s).report = some (run zero fuel s).state :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.run_checked fuel s

theorem replay_prefix {sites : List Nat} (hit : replay zero source sites = some target) (length : Nat) :
    replay zero source (sites.take length) = some (close zero source (sites.take length)) :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.replay_prefix hit length

/-- Soundness also applies to every accepted prefix and to exhausted runs. -/
theorem replay_sound {sites : List Nat} (hit : replay zero source sites = some target)
    (zeroLaw : m.run zero .nil = some ⟨0⟩) : Preserves m env source target :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.replay_eq_close hit ▸
    Dedup.close_sound source sites zeroLaw

theorem check_sound {fuel : Nat} {report : Report} (hit : check zero fuel source report = some target)
    (zeroLaw : m.run zero .nil = some ⟨0⟩) : Preserves m env source target :=
  replay_sound (check_replay.mp hit).1 zeroLaw

theorem check_budget {fuel : Nat} {report : Report} (hit : check zero fuel source report = some target) :
    report.sites.length ≤ fuel :=
  (check_replay.mp hit).2.1

theorem check_retains {fuel : Nat} {report : Report}
    (hit : check zero fuel source report = some target) : Prefix source target :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.replay_eq_close (check_replay.mp hit).1 ▸
    close_retains source report.sites

theorem check_size {fuel : Nat} {report : Report}
    (hit : check zero fuel source report = some target) : target.1 ≤ source.1 + fuel :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.replay_eq_close (check_replay.mp hit).1 ▸
    Nat.le_trans (close_size (zero := zero) source report.sites)
      (Nat.add_le_add_left (check_budget hit) source.1)

theorem check_fixed {fuel : Nat} {report : Report} (hit : check zero fuel source report = some target)
    (stop : report.stop = .fixed) : Fixed zero target :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.check_fixed hit stop

theorem check_exhausted {fuel : Nat} {report : Report}
    (hit : check zero fuel source report = some target) (stop : report.stop = .exhausted) :
    report.sites.length = fuel ∧ ¬ Fixed zero target :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.check_exhausted hit stop

/-- Reachability and stability for this visit policy. It requires no
monotone simulation premise and gives no uniqueness conclusion. -/
theorem check_normalForm {fuel : Nat} {report : Report}
    (hit : check zero fuel source report = some target) (stop : report.stop = .fixed) :
    NormalForms.StableNormalForm Comparable (Visits zero) source target :=
  Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.check_normal hit stop

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist
