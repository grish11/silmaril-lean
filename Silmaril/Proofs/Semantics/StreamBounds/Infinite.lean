module

public import Silmaril.Proofs.Semantics.StreamBounds.Finite
public import Silmaril.Semantics.Streams.Thms

/-! # Proofs: running bounds on infinite words and per-chunk transport bounds -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.StreamBounds

open Cslib Silmaril.Streams

universe u v

variable {α : Type u} {τ : Type v}

theorem mem_safetyω_runBound {f : List α → ℕ} {n : ℕ} {s : ωSequence α} :
    s ∈ safetyω (RunBound f n) ↔ ∀ k, f (s.take k) ≤ n := by
  refine ⟨fun h k => h k _ (List.prefix_refl _), fun h k p hp => ?_⟩
  rw [List.prefix_iff_eq_take.mp hp, ωSequence.take_take]
  exact h _

theorem safetyω_runBound_length (m : ℕ) :
    safetyω (RunBound (List.length : List α → ℕ) m) = ⊥ := by
  refine ωLanguage.mem_ext fun s => iff_of_false (fun h => ?_) (ωLanguage.notMem_bot s)
  have := mem_safetyω_runBound.mp h (m + 1)
  rw [ωSequence.length_take] at this
  omega

theorem gap_replicate (isSep : α → Bool) {sep : α} (h : isSep sep = true) (k : ℕ) :
    gap isSep (List.replicate k sep) = 0 := by
  cases k with
  | zero => rfl
  | succ k => rw [List.replicate_succ', gap_append_singleton]; simp [h]

theorem replicate_mem_itemBound (isSep : α → Bool) {sep : α} (h : isSep sep = true) (k : ℕ) :
    List.replicate k sep ∈ ItemBound isSep 0 := by
  intro p hp
  have : p = List.replicate p.length sep :=
    List.eq_replicate_iff.mpr ⟨rfl, fun b hb => List.eq_of_mem_replicate (hp.subset hb)⟩
  rw [this, gap_replicate isSep h]

theorem gap_take_le_of_sep (isSep : α → Bool) {s : ωSequence α} {j : ℕ}
    (hj : isSep (s j) = true) : ∀ k, j < k → gap isSep (s.take k) ≤ k - j - 1
  | 0, h => absurd h (Nat.not_lt_zero _)
  | k + 1, h => by
    rw [ωSequence.take_succ', gap_append_singleton]
    split
    · exact Nat.zero_le _
    · rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
      · have := gap_take_le_of_sep isSep hj k h; omega
      · simp_all

theorem mem_safetyω_itemBound_of_window {isSep : α → Bool} {n : ℕ} {s : ωSequence α}
    (h : ∀ i, ∃ j, i ≤ j ∧ j ≤ i + n ∧ isSep (s j) = true) :
    s ∈ safetyω (ItemBound isSep n) := by
  refine mem_safetyω_runBound.mpr fun k => ?_
  by_cases hk : k ≤ n
  · exact (gap_le_length isSep _).trans (by rw [ωSequence.length_take]; exact hk)
  · obtain ⟨j, hij, hjn, hj⟩ := h (k - n - 1)
    have := gap_take_le_of_sep isSep hj k (by omega)
    omega

theorem const_mem_safetyω_itemBound {isSep : α → Bool} {sep : α} (h : isSep sep = true)
    (n : ℕ) : ωSequence.const sep ∈ safetyω (ItemBound isSep n) :=
  mem_safetyω_itemBound_of_window fun i => ⟨i, le_rfl, Nat.le_add_right _ _, h⟩

theorem repeatItem_sep (item : List α) (sep : α) (q : ℕ) :
    repeatItem item sep ((item.length + 1) * q + item.length) = sep := by
  have hm : ((item.length + 1) * q + item.length) % (item.length + 1) = item.length := by
    rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt (Nat.lt_succ_self _)
  simp [repeatItem, hm]

theorem repeatItem_mem_safetyω_itemBound {isSep : α → Bool} {item : List α} {sep : α}
    (h : isSep sep = true) {n : ℕ} (hn : item.length ≤ n) :
    repeatItem item sep ∈ safetyω (ItemBound isSep n) := by
  refine mem_safetyω_itemBound_of_window fun i => ?_
  refine ⟨(item.length + 1) * (i / (item.length + 1)) + item.length, ?_, ?_, ?_⟩
  · have := Nat.div_add_mod i (item.length + 1)
    have := Nat.mod_lt i (show 0 < item.length + 1 by omega)
    omega
  · have := Nat.div_add_mod i (item.length + 1)
    omega
  · rw [repeatItem_sep]; exact h

theorem depth_take_of_opening {kind : τ → BracketKind} {s : ωSequence τ}
    (h : ∀ i, kind (s i) = .opening) : ∀ k, depth kind (s.take k) = k
  | 0 => rfl
  | k + 1 => by
    rw [ωSequence.take_succ', depth_append_singleton, depth_take_of_opening h k]
    simp [depthStep, h]

theorem not_mem_safetyω_depthBound {kind : τ → BracketKind} {s : ωSequence τ}
    (h : ∀ i, kind (s i) = .opening) (d : ℕ) : s ∉ safetyω (DepthBound kind d) := by
  intro hs
  have := mem_safetyω_runBound.mp hs (d + 1)
  rw [depth_take_of_opening h] at this
  omega

/-! ## Transport bounds -/

theorem chunkBound_ofList_singletons (w : List α) :
    ChunkBound 1 (Chunks.ofList (w.map fun a => [a])) := by
  intro n
  induction w generalizing n with
  | nil => simp [Chunks.ofList]
  | cons a w ih => cases n <;> simp_all [Chunks.ofList]

theorem limit_ofList_singletons (w : List α) :
    (Chunks.ofList (w.map fun a => [a])).limit = .fin w := by
  rw [Chunks.limit_ofList, ← List.flatMap_def, List.flatMap_singleton']

theorem chunkBound_ofω (s : ωSequence α) : ChunkBound 1 (Chunks.ofω s) :=
  fun _ => le_rfl

theorem chunkBound_mono {k l : ℕ} {cs : Chunks α} (h : ChunkBound k cs) (hkl : k ≤ l) :
    ChunkBound l cs :=
  fun n => (h n).trans hkl

theorem exists_chunkBound_limit {k : ℕ} (hk : 1 ≤ k) (t : Word α) :
    ∃ cs : Chunks α, ChunkBound k cs ∧ cs.limit = t := by
  cases t with
  | fin w => exact ⟨_, chunkBound_mono (chunkBound_ofList_singletons w) hk, limit_ofList_singletons w⟩
  | inf s => exact ⟨_, chunkBound_mono (chunkBound_ofω s) hk, Chunks.limit_ofω s⟩

theorem limit_of_chunkBound_zero {cs : Chunks α} (h : ChunkBound 0 cs) : cs.limit = .fin [] := by
  have hp : ∀ n, cs.prefixAt n = [] := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => rw [Chunks.prefixAt_succ, ih, List.eq_nil_of_length_eq_zero (Nat.le_zero.mp (h n))]; rfl
  exact Chunks.limit_eq_iff.mpr ⟨0, fun n _ => hp n⟩

end Silmaril.Proofs.Semantics.StreamBounds
