module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined.Defs
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Thms
import Silmaril.SSA.Peggy.Worked.EvalScale.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined
open Silmaril.SSA.Peggy.Worked
open Silmaril.SSA.RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {l : Nat}
variable {ops : Ops P} {source target : Output P params results l}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}
private theorem preserves_refl (s : Output P params results l) : Dedup.Preserves m env s s :=
  fun wf valid => ⟨wf, valid, fun _ => rfl⟩

private theorem preserves_trans {s t u : Output P params results l}
    (first : Dedup.Preserves m env s t) (second : Dedup.Preserves m env t u) : Dedup.Preserves m env s u := by
  intro wf valid
  obtain ⟨midWF, midValid, initial⟩ := first wf valid
  obtain ⟨lastWF, lastValid, final⟩ := second midWF midValid
  exact ⟨lastWF, lastValid, fun idx => (final idx).trans (initial idx)⟩

variable [DecidableEq Data] [DecidableEq (P [] .count)] [DecidableEq (P [.count, .count] .count)]

private theorem enabled_mem (s : Output P params results l) (action : Action)
    (hit : enabled ops s action = true) : action ∈ actions s.1 := by
  cases action with
  | zeroSample address =>
    by_cases bound : address < s.1
    · simp [actions, bound]
    · simp [enabled, Dedup.Worklist.enabledAt, bound] at hit
  | evalScale address =>
    by_cases bound : address < s.1
    · simp [actions, bound]
    · simp [enabled, scaleEnabled, bound] at hit

theorem next_none_iff (s : Output P params results l) : (driver ops).next s = none ↔ Fixed ops s := by
  change (actions s.1).find? (enabled ops s) = none ↔ ∀ action, enabled ops s action = false
  rw [List.find?_eq_none]
  constructor
  · intro empty action
    cases hit : enabled ops s action with
    | false => rfl
    | true => exact (empty action (enabled_mem s action hit) hit).elim
  · intro fixed action _ hit
    rw [fixed action] at hit
    cases hit

private theorem scale_sound (s : Output P params results l) (address : Nat)
    (law : EvalScale.Law m ops.factor ops.scale) : Dedup.Preserves m env s (scaleVisit ops s address) := by
  by_cases bound : address < s.1
  · simp only [scaleVisit, dite_eq_left bound]
    cases EvalScale.Match.atSite s.2.graph ⟨address, bound⟩ ops.factor ops.scale with
    | none => exact preserves_refl s
    | some found =>
      change Dedup.Preserves m env s
        (if checkCovered found s.2.classes then s else (found.plan (s := s.2)).run 2)
      split
      · exact preserves_refl s
      · intro wf valid
        exact ⟨found.plan.demandWellFounded 2 wf, found.plan.sound 2 wf valid (found.plan_holds law)⟩
  · simpa only [scaleVisit, dite_eq_right bound] using (preserves_refl (m := m) (env := env) s)

theorem visit_sound (s : Output P params results l) (action : Action)
    (zeroLaw : m.run ops.zero .nil = some ⟨0⟩) (scaleLaw : EvalScale.Law m ops.factor ops.scale) :
    Dedup.Preserves m env s (visit ops s action) := by
  cases action with
  | zeroSample address => exact Dedup.close_sound s [address] zeroLaw
  | evalScale address => exact scale_sound s address scaleLaw

theorem check_sound {fuel : Nat} {report : Report Action}
    (hit : (driver ops).check fuel source report = some target)
    (zeroLaw : m.run ops.zero .nil = some ⟨0⟩) (scaleLaw : EvalScale.Law m ops.factor ops.scale) :
    Dedup.Preserves m env source target :=
  Driver.replay_rel (Dedup.Preserves m env) preserves_refl preserves_trans
    (fun s action _ => visit_sound s action zeroLaw scaleLaw) (Driver.check_iff.mp hit).1

theorem check_exhausted {fuel : Nat} {report : Report Action}
    (hit : (driver ops).check fuel source report = some target) (stop : report.stop = .exhausted) :
    report.sites.length = fuel ∧ ¬ Fixed ops target := by
  obtain ⟨budget, more⟩ := Driver.check_exhausted hit stop
  refine ⟨budget, fun fixed => ?_⟩
  rw [(next_none_iff target).mpr fixed] at more
  cases more

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Worklist.Combined
