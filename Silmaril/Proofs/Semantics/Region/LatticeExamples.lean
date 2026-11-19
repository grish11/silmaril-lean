module

public import Silmaril.Semantics.Region.Abstract.Examples.Defs
public import Silmaril.Semantics.Region.Abstract.Named.Thms

@[expose] public section
namespace Silmaril.Semantics.Region.Abstract.Examples.Proofs

theorem left_closed : Closed rules left := by
  intro r hr premises
  obtain rfl : r = composition := Set.mem_singleton_iff.mp hr
  have h := premises (show atom 1 ∈ composition.premises by simp [composition])
  simp [left, atom] at h

theorem right_closed : Closed rules right := by
  intro r hr premises
  obtain rfl : r = composition := Set.mem_singleton_iff.mp hr
  have h := premises (show atom 0 ∈ composition.premises by simp [composition])
  simp [right, atom] at h

theorem union_not_closed : ¬ Closed rules (left ∪ right) := by
  intro closed
  have h := closed composition (by simp [rules]) (show composition.premises ⊆ left ∪ right by
    intro a ha
    simpa [composition, left, right, or_comm] using ha)
  simp [composition, left, right, atom] at h

theorem composed_in_join (hl : Closed rules left) (hr : Closed rules right) :
    atom 2 ∈ ((⟨left, hl⟩ : ClosedModel rules) ⊔ ⟨right, hr⟩).val := by
  apply closure_closed (left ∪ right) composition (by simp [rules])
  intro a ha
  apply subset_closure (left ∪ right)
  simpa [composition, left, right, or_comm] using ha

theorem forget_not_meet :
    forget (fun _ : Atom => ()) (left ∩ right) ≠
      forget (fun _ : Atom => ()) left ∩ forget (fun _ : Atom => ()) right := by
  intro eq
  have h : () ∈ forget (fun _ : Atom => ()) left ∩ forget (fun _ : Atom => ()) right :=
    ⟨⟨atom 0, by simp [left], rfl⟩, ⟨atom 1, by simp [right], rfl⟩⟩
  rw [← eq] at h
  obtain ⟨a, ⟨hl, hr⟩, _⟩ := h
  have eq01 := (Set.mem_singleton_iff.mp hl).symm.trans (Set.mem_singleton_iff.mp hr)
  have bad := congrArg LabelAtom.entry eq01
  simp [atom] at bad

theorem nonempty_not_meet : left.Nonempty ∧ right.Nonempty ∧ ¬ (left ∩ right).Nonempty := by
  refine ⟨⟨atom 0, rfl⟩, ⟨atom 1, rfl⟩, ?_⟩
  rintro ⟨a, hl, hr⟩
  have eq01 := (Set.mem_singleton_iff.mp hl).symm.trans (Set.mem_singleton_iff.mp hr)
  have bad := congrArg LabelAtom.entry eq01
  simp [atom] at bad

end Silmaril.Semantics.Region.Abstract.Examples.Proofs
