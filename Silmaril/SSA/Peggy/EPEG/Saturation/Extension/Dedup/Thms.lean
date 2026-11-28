module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Checker
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Step
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Closure

public section

namespace Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup

open PEG
open RVSDG (Tuple)
open Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {site i : Fin n} {zero : P [] .count}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}
variable [DecidableEq Data]

theorem checkRhs_iff (found : ZeroSample g site zero) :
    checkRhs found i = true ↔ RhsAt found i :=
  check_rhs_iff found

theorem checkCovered_iff (found : ZeroSample g site zero) (classes : Classes n) :
    checkCovered found classes = true ↔ Covered found classes :=
  check_covered_iff found classes

theorem choose_keep_iff (found : ZeroSample g site zero) (classes : Classes n) :
    choose found classes = .keep ↔ Covered found classes :=
  keep_iff found classes

theorem choose_reuse_sound (found : ZeroSample g site zero) (classes : Classes n)
    (choice : choose found classes = .reuse i) : RhsAt found i :=
  reuse_sound found classes choice

theorem choose_append_iff (found : ZeroSample g site zero) (classes : Classes n) :
    choose found classes = .append ↔ ∀ i, ¬ RhsAt found i :=
  append_iff found classes

variable {s : State P params results n l}

theorem ensure_complete (found : ZeroSample s.graph site zero) :
    Prefix ⟨n, s⟩ (ensure found) ∧ CompleteAt zero (ensure found) site.val :=
  ensure_cert found

theorem ensure_sound (found : ZeroSample s.graph site zero)
    (zeroLaw : m.run zero .nil = some ⟨0⟩) : Preserves m env ⟨n, s⟩ (ensure found) :=
  ensure_preserves found zeroLaw

variable [DecidableEq (P [] .count)]

theorem checkDone_iff (s : Output P params results l) (address : Nat) :
    checkDone zero s address = true ↔ CompleteAt zero s address :=
  check_done_iff s address

theorem checkClosed_iff (s : Output P params results l) (sites : List Nat) :
    checkClosed zero s sites = true ↔ ∀ address ∈ sites, CompleteAt zero s address := by
  simp only [checkClosed, List.all_eq_true, checkDone_iff]

theorem visit_stutters {s : Output P params results l} {address : Nat}
    (done : checkDone zero s address = true) : visit zero s address = s :=
  visit_done ((checkDone_iff s address).mp done)

theorem close_retains (s : Output P params results l) (sites : List Nat) :
    Prefix s (close zero s sites) :=
  close_prefix s sites

theorem close_size (s : Output P params results l) (sites : List Nat) :
    (close zero s sites).1 ≤ s.1 + sites.length :=
  close_bound s sites

/-- Every supplied, initially eligible site is covered after one traversal. -/
theorem close_checked (s : Output P params results l) (sites : List Nat)
    (eligible : ∀ address ∈ sites, EligibleAt zero s address) :
    checkClosed zero (close zero s sites) sites = true :=
  (checkClosed_iff _ _).mpr (close_complete s sites eligible)

/-- A completed scope has no further visit that changes the state. -/
theorem close_fixed (s : Output P params results l) (sites : List Nat)
    (closed : checkClosed zero s sites = true) : close zero s sites = s :=
  close_stutters s sites ((checkClosed_iff _ _).mp closed)

theorem close_sound (s : Output P params results l) (sites : List Nat)
    (zeroLaw : m.run zero .nil = some ⟨0⟩) : Preserves m env s (close zero s sites) :=
  close_preserves s sites zeroLaw

end Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup
