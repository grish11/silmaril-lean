module

public import Silmaril.Semantics.StreamBounds.Defs
import Silmaril.Proofs.Semantics.StreamBounds.Finite

/-! # Proofs: framed item lists and per-item bounds -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.StreamBounds

open Silmaril.Streams

universe u

variable {α : Type u}

theorem runBound_concat {f : List α → ℕ} {n : ℕ} (w : List α) (a : α) :
    w ++ [a] ∈ RunBound f n ↔ w ∈ RunBound f n ∧ f (w ++ [a]) ≤ n := by
  constructor
  · intro h
    exact ⟨fun p hp => h p (hp.trans (List.prefix_append _ _)), h _ (List.prefix_refl _)⟩
  · rintro ⟨h, ha⟩ p hp
    rcases List.prefix_concat_iff.mp hp with rfl | hp
    · exact ha
    · exact h p hp

theorem gap_append_sepFree (isSep : α → Bool) (u x : List α) (hx : ∀ a ∈ x, isSep a = false) :
    gap isSep (u ++ x) = gap isSep u + x.length := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih =>
    have ha : isSep a = false := hx a (by simp)
    rw [← List.append_assoc, gap_append_singleton, ha, ih (fun b hb => hx b (by simp [hb]))]
    simp [Nat.add_assoc]

theorem itemBound_append_sepFree {isSep : α → Bool} {n : ℕ} (u x : List α)
    (hu : gap isSep u = 0) (hx : ∀ a ∈ x, isSep a = false) :
    u ++ x ∈ ItemBound isSep n ↔ u ∈ ItemBound isSep n ∧ x.length ≤ n := by
  induction x using List.reverseRecOn with
  | nil => simp
  | append_singleton x a ih =>
    have hx' : ∀ b ∈ x, isSep b = false := fun b hb => hx b (by simp [hb])
    have hg : gap isSep (u ++ x ++ [a]) = (x ++ [a]).length := by
      rw [List.append_assoc, gap_append_sepFree isSep u (x ++ [a]) hx, hu, Nat.zero_add]
    rw [← List.append_assoc, ItemBound, runBound_concat, ← ItemBound, ih hx', hg,
      List.length_append, List.length_singleton]
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, by omega⟩, h3⟩

theorem frameItems_append (sep : α) (xs : List (List α)) (x : List α) :
    frameItems sep (xs ++ [x]) = frameItems sep xs ++ x ++ [sep] := by
  simp [frameItems, List.append_assoc]

theorem gap_frameItems {isSep : α → Bool} {sep : α} (h : isSep sep = true)
    (items : List (List α)) : gap isSep (frameItems sep items) = 0 := by
  induction items using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x _ => rw [frameItems_append, gap_append_singleton, h]; rfl

theorem frameItems_mem_itemBound_iff {isSep : α → Bool} {sep : α} {n : ℕ} (h : isSep sep = true)
    (items : List (List α)) (hs : ∀ x ∈ items, ∀ a ∈ x, isSep a = false) :
    frameItems sep items ∈ ItemBound isSep n ↔ ∀ x ∈ items, x.length ≤ n := by
  induction items using List.reverseRecOn with
  | nil =>
    refine iff_of_true (fun p hp => ?_) (by simp)
    rw [show frameItems sep [] = [] from rfl, List.prefix_nil] at hp
    subst hp; exact Nat.zero_le _
  | append_singleton xs x ih =>
    have hxs : ∀ y ∈ xs, ∀ a ∈ y, isSep a = false := fun y hy => hs y (by simp [hy])
    have hx : ∀ a ∈ x, isSep a = false := hs x (by simp)
    rw [frameItems_append, ItemBound, runBound_concat, ← ItemBound,
      itemBound_append_sepFree _ _ (gap_frameItems h xs) hx, ih hxs, gap_append_singleton, h]
    simp [or_imp, forall_and]

end Silmaril.Proofs.Semantics.StreamBounds
