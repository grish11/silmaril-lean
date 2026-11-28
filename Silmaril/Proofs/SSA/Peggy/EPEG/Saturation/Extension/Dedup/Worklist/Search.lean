module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist.Defs
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Thms
import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Comparison.Thms

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {l : Nat}
variable {zero : P [] .count}
variable [DecidableEq Data] [DecidableEq (P [] .count)]

theorem enabled_iff (s : Output P params results l) (i : Fin s.1) :
    enabled zero s i = true ↔ ∃ found : ZeroSample s.2.graph i zero, ¬ Covered found s.2.classes := by
  unfold enabled
  cases hit : ZeroSample.matchAt (g := s.2.graph) i zero with
  | none =>
    constructor
    · intro impossible
      cases impossible
    · rintro ⟨found, _⟩
      rw [found.matchAt_of_witness] at hit
      cases hit
  | some found =>
    change (!checkCovered found s.2.classes) = true ↔
      ∃ other : ZeroSample s.2.graph i zero, ¬ Covered other s.2.classes
    have uncovered_iff : (!checkCovered found s.2.classes) = true ↔ ¬ Covered found s.2.classes := by
      rw [← checkCovered_iff]
      cases checkCovered found s.2.classes <;> decide
    constructor
    · exact fun uncovered => ⟨found, uncovered_iff.mp uncovered⟩
    · rintro ⟨other, uncovered⟩
      have same := Option.some.inj (hit.symm.trans other.matchAt_of_witness)
      subst other
      exact uncovered_iff.mpr uncovered

theorem next_none_iff (s : Output P params results l) :
    next zero s = none ↔ Fixed zero s := by
  unfold next Fixed
  rw [List.find?_eq_none]
  constructor
  · intro absent i found
    apply Classical.byContradiction
    intro uncovered
    exact absent i (List.mem_finRange i) ((enabled_iff s i).mpr ⟨found, uncovered⟩)
  · intro done i _ enabled
    obtain ⟨found, uncovered⟩ := (enabled_iff s i).mp enabled
    exact uncovered (done i found)

theorem next_enabled (s : Output P params results l) (i : Fin s.1)
    (pick : next zero s = some i) : enabledAt zero s i.val = true := by
  have hit := List.find?_some pick
  obtain ⟨address, bound⟩ := i
  unfold enabledAt
  rw [dite_eq_left bound]
  exact hit

theorem fixed_visit (s : Output P params results l) (address : Nat)
    (closed : Fixed zero s) : visit zero s address = s := by
  by_cases bound : address < s.1
  · cases hit : ZeroSample.matchAt (g := s.2.graph) ⟨address, bound⟩ zero with
    | none => simp [visit, bound, hit]
    | some found =>
      apply Dedup.visit_stutters
      apply (checkDone_iff s address).mpr
      exact ⟨⟨address, bound⟩, found, rfl, closed _ found⟩
  · simp [visit, bound]

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Worklist
