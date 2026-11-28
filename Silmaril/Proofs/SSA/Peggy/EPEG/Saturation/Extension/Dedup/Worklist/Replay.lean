module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Search
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist (Driver)
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist
open Silmaril.SSA.RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {l : Nat}
variable {zero : P [] .count} {source target : Output P params results l}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}
variable [DecidableEq Data] [DecidableEq (P [] .count)]

theorem check_iff {fuel : Nat} {report : Report} :
    check zero fuel source report = some target ↔
      replay zero source report.sites = some target ∧
        report.sites.length ≤ fuel ∧ checkStop zero fuel target report = true :=
  Driver.check_iff

theorem replay_eq_close {sites : List Nat} (hit : replay zero source sites = some target) :
    close zero source sites = target := by
  induction sites generalizing source with
  | nil => exact Option.some.inj hit
  | cons i rest ih =>
    unfold replay Driver.replay at hit
    split at hit
    · exact ih hit
    · cases hit

theorem replay_prefix {sites : List Nat} (hit : replay zero source sites = some target) (length : Nat) :
    replay zero source (sites.take length) = some (close zero source (sites.take length)) := by
  induction length generalizing source sites with
  | zero => rfl
  | succ length ih =>
    cases sites with
    | nil => rfl
    | cons address rest =>
      unfold replay Driver.replay at hit
      split at hit
      · rename_i enabled
        have active : enabledAt zero source address = true := enabled
        simpa only [List.take_succ_cons, replay, Driver.replay, driver, ite_eq_left active,
          close, List.foldl_cons] using ih hit
      · cases hit

theorem closed_iff (s : Output P params results l) : checkFixed zero s = true ↔ Fixed zero s := by
  simpa only [checkFixed, Option.isNone_iff_eq_none] using (next_none_iff (zero := zero) s)

theorem check_fixed {fuel : Nat} {report : Report} (hit : check zero fuel source report = some target)
    (stop : report.stop = .fixed) : Fixed zero target := by
  apply (next_none_iff target).mp
  have empty := Driver.check_fixed hit stop
  simpa [driver] using empty

theorem check_exhausted {fuel : Nat} {report : Report}
    (hit : check zero fuel source report = some target) (stop : report.stop = .exhausted) :
    report.sites.length = fuel ∧ ¬ Fixed zero target := by
  obtain ⟨budget, more⟩ := Driver.check_exhausted hit stop
  refine ⟨budget, fun finished => ?_⟩
  simp [driver, (next_none_iff target).mpr finished] at more

theorem run_checked (fuel : Nat) (s : Output P params results l) :
    check zero fuel s (run zero fuel s).report = some (run zero fuel s).state := by
  apply Driver.run_checked
  intro state address picked
  obtain ⟨site, hit, rfl⟩ := Option.map_eq_some_iff.mp picked
  exact next_enabled state site hit

private theorem visit_reachable (sites : List Nat) (s : Output P params results l) :
    Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms.Reachable (Visits zero) s (close zero s sites) := by
  induction sites generalizing s with
  | nil => exact .refl
  | cons address rest ih =>
    exact Relation.ReflTransGen.head ⟨address, rfl⟩ (ih (visit zero s address))

theorem check_normal {fuel : Nat} {report : Report} (hit : check zero fuel source report = some target)
    (stop : report.stop = .fixed) : Silmaril.SSA.Peggy.EPEG.Saturation.NormalForms.StableNormalForm Comparable (Visits zero) source target := by
  constructor
  · rw [← replay_eq_close (check_iff.mp hit).1]
    exact visit_reachable report.sites source
  · rintro other ⟨address, rfl⟩
    rw [fixed_visit target address (check_fixed hit stop)]
    exact Comparable.refl target

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist
