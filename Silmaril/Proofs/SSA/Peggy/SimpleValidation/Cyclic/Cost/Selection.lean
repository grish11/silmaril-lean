module

public import Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost.Defs

public section

namespace Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG (Classes)
open Silmaril.SSA.Peggy.SimpleValidation.Cyclic.Cost

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n : Nat}
variable {source : Graph P params results n 1} {classes : Classes n}
variable {Certificate : Candidate source → Type w} {emit : ∀ c, Option (Certificate c)}
variable {cost : Candidate source → Nat} {pool : List (Candidate source)}
variable {chosen : Checked source classes Certificate}

private theorem check_candidate {candidate : Candidate source} {a : Checked source classes Certificate}
    (checked : candidate.checkWith classes emit = some a) : a.candidate = candidate := by
  unfold Candidate.checkWith at checked
  split at checked
  · cases checked
  · obtain ⟨_, _, eq⟩ := Option.map_eq_some_iff.mp checked
    exact congrArg Checked.candidate eq.symm

theorem selected (found : selectWith classes emit cost pool = some chosen) :
    chosen.candidate ∈ pool ∧ chosen.candidate.checkWith classes emit = some chosen := by
  obtain ⟨candidate, member, checked⟩ := List.mem_filterMap.mp (List.minOn?_mem found)
  rw [check_candidate checked]
  exact ⟨member, checked⟩

theorem minimal (found : selectWith classes emit cost pool = some chosen) {other : Candidate source}
    (member : other ∈ pool) (admitted : (other.checkWith classes emit).isSome = true) :
    cost chosen.candidate ≤ cost other := by
  obtain ⟨a, checked⟩ := Option.isSome_iff_exists.mp admitted
  have kept : a ∈ pool.filterMap (Candidate.checkWith classes emit) :=
    List.mem_filterMap.mpr ⟨other, member, checked⟩
  unfold selectWith at found
  simpa [found, check_candidate checked] using
    List.apply_get_minOn?_le_of_mem (f := fun a => cost a.candidate) kept

theorem select_none :
    selectWith classes emit cost pool = none ↔ ∀ candidate ∈ pool, candidate.checkWith classes emit = none := by
  rw [← Option.isNone_iff_eq_none]
  simp [selectWith, Option.isNone_iff_eq_none, List.minOn?_eq_ite]

end Silmaril.Proofs.SSA.Peggy.SimpleValidation.Cyclic.Cost
