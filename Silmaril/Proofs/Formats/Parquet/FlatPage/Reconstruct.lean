module

public import Silmaril.Formats.Parquet.FlatPage.Defs
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.FlatPage

open Silmaril.Formats.Parquet.FlatPage

private theorem reconstructLoop_sound {α : Type} {mask : List Bool} {values : List α}
    {acc out : List (Option α)} (h : reconstructLoop mask values acc = .ok out) :
    ∃ slots : List (Option α), out = acc.reverse ++ slots ∧
      slots.map Option.isSome = mask ∧ slots.filterMap id = values := by
  induction mask generalizing values acc out with
  | nil =>
    cases values with
    | nil =>
      cases h
      exact ⟨[], by simp⟩
    | cons => simp [reconstructLoop] at h
  | cons bit mask ih =>
    cases bit with
    | false =>
      obtain ⟨slots, outEq, shape, order⟩ := ih h
      exact ⟨none :: slots, by simpa [List.append_assoc] using outEq, by simp [shape], by simp [order]⟩
    | true =>
      cases values with
      | nil => simp [reconstructLoop] at h
      | cons value values =>
        obtain ⟨slots, outEq, shape, order⟩ := ih h
        exact ⟨some value :: slots, by simpa [List.append_assoc] using outEq,
          by simp [shape], by simp [order]⟩

private theorem reconstructLoop_project {α : Type} (slots acc : List (Option α)) :
    reconstructLoop (slots.map Option.isSome) (slots.filterMap id) acc =
      .ok (acc.reverse ++ slots) := by
  induction slots generalizing acc with
  | nil => simp [reconstructLoop]
  | cons slot slots ih =>
    cases slot <;> simp [reconstructLoop, ih, List.append_assoc]

public theorem reconstruct_ok_iff {α : Type} {mask : List Bool} {values : List α}
    {slots : List (Option α)} :
    reconstruct mask values = .ok slots ↔
      slots.map Option.isSome = mask ∧ slots.filterMap id = values := by
  constructor
  · intro h
    obtain ⟨out, eq, shape, order⟩ := reconstructLoop_sound h
    have same : slots = out := by simpa using eq
    subst slots
    exact ⟨shape, order⟩
  · rintro ⟨rfl, rfl⟩
    simpa [reconstruct] using reconstructLoop_project slots []

public theorem present_count_eq {α : Type} (slots : List (Option α)) :
    (slots.map Option.isSome).count true = (slots.filterMap id).length := by
  induction slots with
  | nil => rfl
  | cons slot slots ih => cases slot <;> simp [ih]

private theorem slots_exist {α : Type} {mask : List Bool} {values : List α}
    (h : mask.count true = values.length) :
    ∃ slots : List (Option α), slots.map Option.isSome = mask ∧ slots.filterMap id = values := by
  induction mask generalizing values with
  | nil =>
    cases values with
    | nil => exact ⟨[], rfl, rfl⟩
    | cons => simp at h
  | cons bit mask ih =>
    cases bit with
    | false =>
      obtain ⟨slots, shape, order⟩ := ih (by simpa using h)
      exact ⟨none :: slots, by simp [shape], by simp [order]⟩
    | true =>
      cases values with
      | nil => simp at h
      | cons value values =>
        obtain ⟨slots, shape, order⟩ := ih (by simpa using h)
        exact ⟨some value :: slots, by simp [shape], by simp [order]⟩

public theorem reconstruct_exists_iff {α : Type} (mask : List Bool) (values : List α) :
    (∃ slots, reconstruct mask values = .ok slots) ↔ mask.count true = values.length := by
  constructor
  · rintro ⟨slots, h⟩
    obtain ⟨shape, order⟩ := reconstruct_ok_iff.mp h
    rw [← shape, ← order, present_count_eq]
  · intro h
    obtain ⟨slots, shape, order⟩ := slots_exist h
    exact ⟨slots, reconstruct_ok_iff.mpr ⟨shape, order⟩⟩

end Silmaril.Proofs.Formats.Parquet.FlatPage
