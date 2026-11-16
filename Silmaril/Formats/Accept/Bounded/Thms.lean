module

public import Silmaril.Formats.Accept.Bounded.Defs
public import Silmaril.Formats.Accept.Bounds.Thms
public import Silmaril.Semantics.Accept.Bounded.Thms

/-! # Bounded soundness and completeness: theorems

* Agreement with the checker forms of `Silmaril.Semantics.Accept.Bounded`
  (`soundWithin_ofBool_iff`, `completeWithin_ofBool_iff`); `univ` is the unbounded notion.
* Bounded notions shrink with the domain (`CompleteWithin.anti`) and transport along
  encodings (`completeWithin_encode_iff`, along an injective encoding).
* **A finite acceptor set is complete for no infinite specification**
  (`not_complete_of_finite`); it is complete within a domain only where the specification
  is finite there (`finite_of_completeWithin`). For byte languages, completeness within a
  length bound is consistent with finiteness, as the bound's slice is finite
  (`ByteLang.finite_upTo`).
-/

@[expose] public section

namespace Silmaril.Formats.Accept.Lang

universe u v

variable {α : Type u} {β : Type v} {A S D D' : Lang α}

theorem soundWithin_ofBool_iff {check : α → Bool} :
    SoundWithin D (Silmaril.Accept.ofBool check) S ↔ Silmaril.Accept.SoundOn D check S :=
  ⟨fun h _ ha hc => h ⟨hc, ha⟩, fun h _ ⟨hc, ha⟩ => h _ ha hc⟩

theorem completeWithin_ofBool_iff {check : α → Bool} :
    CompleteWithin D (Silmaril.Accept.ofBool check) S ↔ Silmaril.Accept.CompleteOn D check S :=
  ⟨fun h _ ha hs => h ⟨hs, ha⟩, fun h _ ⟨hs, ha⟩ => h _ ha hs⟩

@[simp] theorem completeWithin_univ : CompleteWithin Set.univ A S ↔ Complete A S := by
  simp [CompleteWithin, Complete]

@[simp] theorem soundWithin_univ : SoundWithin Set.univ A S ↔ Sound A S := by
  simp [SoundWithin, Sound]

theorem exactWithin_iff : ExactWithin D A S ↔ SoundWithin D A S ∧ CompleteWithin D A S := by
  constructor
  · intro h
    exact ⟨fun x hx => (h ▸ hx).1, fun x hx => (h.symm ▸ hx).1⟩
  · rintro ⟨hs, hc⟩
    ext x
    exact ⟨fun hx => ⟨hs hx, hx.2⟩, fun hx => ⟨hc hx, hx.2⟩⟩

theorem Complete.completeWithin (h : Complete A S) (D : Lang α) : CompleteWithin D A S :=
  fun _ hx => h hx.1

theorem Sound.soundWithin (h : Sound A S) (D : Lang α) : SoundWithin D A S :=
  fun _ hx => h hx.1

theorem CompleteWithin.anti (h : CompleteWithin D A S) (hD : D' ⊆ D) : CompleteWithin D' A S :=
  fun _ hx => h ⟨hx.1, hD hx.2⟩

theorem SoundWithin.anti (h : SoundWithin D A S) (hD : D' ⊆ D) : SoundWithin D' A S :=
  fun _ hx => h ⟨hx.1, hD hx.2⟩

/-- Along an injective encoding, bounded completeness is preserved and reflected. -/
theorem completeWithin_encode_iff {e : α → β} (he : Function.Injective e) :
    CompleteWithin (D.encode e) (A.encode e) (S.encode e) ↔ CompleteWithin D A S := by
  unfold CompleteWithin encode
  rw [← Set.image_inter he]
  exact Set.image_subset_image_iff he

/-- Along an injective encoding, bounded soundness is preserved and reflected. -/
theorem soundWithin_encode_iff {e : α → β} (he : Function.Injective e) :
    SoundWithin (D.encode e) (A.encode e) (S.encode e) ↔ SoundWithin D A S := by
  unfold SoundWithin encode
  rw [← Set.image_inter he]
  exact Set.image_subset_image_iff he

/-! ## Finite acceptors -/

/-- **A finite acceptor set is complete for no infinite specification.** -/
theorem not_complete_of_finite (hA : A.Finite) (hS : S.Infinite) : ¬ Complete A S :=
  fun h => hS (hA.subset h)

/-- Bounded completeness of a finite acceptor set forces the specification to be finite on
the domain. -/
theorem finite_of_completeWithin (hA : A.Finite) (h : CompleteWithin D A S) : (S ∩ D).Finite :=
  hA.subset h

end Silmaril.Formats.Accept.Lang
