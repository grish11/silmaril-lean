module

public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Defs
import Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup.Step

public section

namespace Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup

open Silmaril.SSA.PEG
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension
open Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Dedup
open Silmaril.SSA.RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {l : Nat}
variable {zero : P [] .count}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params}
variable [DecidableEq Data] [DecidableEq (P [] .count)]

theorem close_prefix (s : Output P params results l) (sites : List Nat) : Prefix s (close zero s sites) := by
  induction sites generalizing s with
  | nil => exact prefix_refl _
  | cons address rest ih => exact prefix_trans (visit_prefix s address) (ih (visit zero s address))

private theorem visit_bound (s : Output P params results l) (address : Nat) :
    (visit zero s address).1 ≤ s.1 + 1 := by
  unfold visit
  split
  · split
    · unfold ensure
      split <;> dsimp only <;> omega
    · omega
  · omega

theorem close_bound (s : Output P params results l) (sites : List Nat) :
    (close zero s sites).1 ≤ s.1 + sites.length := by
  induction sites generalizing s with
  | nil => exact Nat.le_refl _
  | cons address rest ih =>
    have tail := ih (visit zero s address)
    have head := visit_bound (zero := zero) s address
    change (close zero (visit zero s address) rest).1 ≤ s.1 + (address :: rest).length
    simp only [List.length_cons]
    omega

theorem close_complete (s : Output P params results l) (sites : List Nat)
    (eligible : ∀ site ∈ sites, EligibleAt zero s site) :
    ∀ site ∈ sites, CompleteAt zero (close zero s sites) site := by
  induction sites generalizing s with
  | nil => simp
  | cons head tail ih =>
    intro address member
    let next := visit zero s head
    have inclusion : Prefix s next := visit_prefix s head
    change CompleteAt zero (close zero next tail) address
    rcases List.mem_cons.mp member with rfl | later
    · exact complete_prefix (close_prefix next tail)
        (visit_complete (eligible _ List.mem_cons_self))
    · exact ih next (fun i occurs => eligible_prefix inclusion (eligible i (List.mem_cons_of_mem _ occurs)))
        address later

theorem close_preserves (s : Output P params results l) (sites : List Nat)
    (zeroLaw : m.run zero .nil = some ⟨0⟩) : Preserves m env s (close zero s sites) := by
  induction sites generalizing s with
  | nil => exact fun wf valid => ⟨wf, valid, fun _ => rfl⟩
  | cons address rest ih =>
    intro wf valid
    have next := visit_preserves s address zeroLaw wf valid
    obtain ⟨nextWF, nextValid, first⟩ := next
    obtain ⟨finalWF, finalValid, later⟩ := ih (visit zero s address) nextWF nextValid
    exact ⟨finalWF, finalValid, fun i => (later i).trans (first i)⟩

theorem close_stutters (s : Output P params results l) (sites : List Nat)
    (done : ∀ address ∈ sites, CompleteAt zero s address) : close zero s sites = s := by
  induction sites with
  | nil => rfl
  | cons head tail ih =>
    change close zero (visit zero s head) tail = s
    rw [visit_done (done head List.mem_cons_self)]
    exact ih (fun address member => done address (List.mem_cons_of_mem _ member))

end Silmaril.Proofs.SSA.Peggy.EPEG.Saturation.Extension.Dedup
