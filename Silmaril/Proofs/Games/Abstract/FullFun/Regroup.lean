module

public import Silmaril.Games.Abstract.FullFun.Defs
import Silmaril.Proofs.Games.Abstract.FullFun.Unfold
import Silmaril.Proofs.Games.Abstract.ModuleInf.Basic

/-!
# Regrouping concatenated streams (proofs)

Stream bookkeeping for the Conway laws of iteration.

* `streamConcat_regroup`: a concatenated stream is the concatenation of consecutive blocks of
  its segments, cut at the indices of a strictly increasing `k` with `k 0 = 0`;
* `streamConcat_drop`: a concatenated stream is its first `M` segments in front of the
  concatenation of the rest;
* `streamConcat_interleave`, `streamConcat_interleave_tail`: the concatenation of
  `a 0 ++ b 0, a 1 ++ b 1, …` is `a 0` in front of the concatenation of
  `b 0 ++ a 1, b 1 ++ a 2, …`.
-/

@[expose] public section

namespace Silmaril.Proofs.Games.Abstract.FullFun

open Silmaril.Games Silmaril.Games.Abstract

universe u

variable {α : Type u}

theorem append_appendStream (l₁ l₂ : List α) (ω : Nat → α) :
    (l₁ ++ l₂) ++ₛ ω = l₁ ++ₛ (l₂ ++ₛ ω) :=
  Stream'.append_append_stream _ _ _

theorem nil_appendStream (ω : Nat → α) : ([] : List α) ++ₛ ω = ω := rfl

/-- The segments of `l` from `k n` to `k (n + 1)`, joined. -/
def regroup (l : Nat → List α) (k : Nat → Nat) (n : Nat) : List α :=
  (List.range (k (n + 1) - k n)).flatMap fun i => l (k n + i)

theorem flatMap_range_add (l : Nat → List α) (a b : Nat) :
    (List.range (a + b)).flatMap l =
      (List.range a).flatMap l ++ (List.range b).flatMap fun i => l (a + i) := by
  rw [List.range_add, List.flatMap_append, List.flatMap_map]

theorem flatMap_regroup (l : Nat → List α) {k : Nat → Nat} (hk0 : k 0 = 0) (hk : Monotone k)
    (n : Nat) : (List.range n).flatMap (regroup l k) = (List.range (k n)).flatMap l := by
  induction n with
  | zero => simp [hk0]
  | succ n ih =>
    rw [ModuleInf.range_flatMap_succ, ih, regroup, ← flatMap_range_add]
    congr 2
    have := hk (Nat.le_succ n)
    simp only [Nat.succ_eq_add_one] at this ⊢
    omega

/-- **Regrouping**: cutting the segments into consecutive blocks keeps the concatenation. -/
theorem streamConcat_regroup {l : Nat → List α} {k : Nat → Nat} (hk0 : k 0 = 0)
    (hk : StrictMono k) (ω : Nat → α) :
    Shape.StreamConcat (regroup l k) ω ↔ Shape.StreamConcat l ω := by
  have hf := flatMap_regroup l hk0 hk.monotone
  constructor
  · rintro ⟨hp, hu⟩
    refine ⟨fun m => ?_, fun N => ?_⟩
    · have := hp m
      rw [hf] at this
      exact ModuleInf.streamPrefix_mono this (ModuleInf.range_flatMap_mono l (hk.id_le m))
    · obtain ⟨n, hn⟩ := hu N
      exact ⟨k n, by rwa [hf] at hn⟩
  · rintro ⟨hp, hu⟩
    refine ⟨fun n => by rw [hf]; exact hp (k n), fun N => ?_⟩
    obtain ⟨m, hm⟩ := hu N
    refine ⟨m, ?_⟩
    rw [hf]
    exact le_trans hm (ModuleInf.range_flatMap_mono l (hk.id_le m)).length_le

/-- **Dropping segments**: a concatenated stream is its first `M` segments in front of the
concatenation of the rest. -/
theorem streamConcat_drop {l : Nat → List α} {ω : Nat → α} (h : Shape.StreamConcat l ω) :
    ∀ M, ∃ ω', ω = (List.range M).flatMap l ++ₛ ω' ∧
      Shape.StreamConcat (fun n => l (M + n)) ω'
  | 0 => ⟨ω, rfl, by simpa using h⟩
  | M + 1 => by
    obtain ⟨ω', rfl, h'⟩ := streamConcat_drop h M
    obtain ⟨he, ht⟩ := streamConcat_tail h'
    simp only [Nat.add_zero] at he ht
    refine ⟨_, ?_, by simpa [Nat.add_assoc, Nat.add_comm 1] using ht⟩
    rw [ModuleInf.range_flatMap_succ]
    exact (congrArg (fun w => (List.range M).flatMap l ++ₛ w) he).trans
      (Stream'.append_append_stream _ _ _).symm

/-- Interleave two sequences of segments: `a 0, b 0, a 1, b 1, …`. -/
def interleave (a b : Nat → List α) (i : Nat) : List α :=
  if i % 2 = 0 then a (i / 2) else b (i / 2)

theorem regroup_interleave (a b : Nat → List α) (n : Nat) :
    regroup (interleave a b) (fun n => 2 * n) n = a n ++ b n := by
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n + 1) % 2 = 1 := by omega
  have h3 : (2 * n) / 2 = n := by omega
  have h4 : (2 * n + 1) / 2 = n := by omega
  have h5 : 2 * (n + 1) - 2 * n = 2 := by omega
  simp [regroup, h5, List.range_succ, interleave, h3, h4]

theorem interleave_succ (a b : Nat → List α) (i : Nat) :
    interleave a b (i + 1) = interleave b (fun n => a (n + 1)) i := by
  unfold interleave
  by_cases h : i % 2 = 0
  · have h' : (i + 1) % 2 ≠ 0 := by omega
    have h'' : (i + 1) / 2 = i / 2 := by omega
    simp [h, h', h'']
  · have h' : (i + 1) % 2 = 0 := by omega
    have h'' : (i + 1) / 2 = i / 2 + 1 := by omega
    simp [h, h', h'']

theorem strictMono_two_mul : StrictMono fun n : Nat => 2 * n := fun _ _ h => by dsimp only; omega

theorem interleave_zero (a b : Nat → List α) : interleave a b 0 = a 0 := rfl

/-- Concatenating the interleaving is concatenating the joined pairs. -/
theorem streamConcat_interleave_iff {a b : Nat → List α} {ω : Nat → α} :
    Shape.StreamConcat (interleave a b) ω ↔ Shape.StreamConcat (fun n => a n ++ b n) ω := by
  rw [← streamConcat_regroup (by rfl) strictMono_two_mul]
  rw [show regroup (interleave a b) (fun n => 2 * n) = fun n => a n ++ b n from
    funext (regroup_interleave a b)]

theorem interleave_shift (a b : Nat → List α) :
    (fun n => interleave a b (n + 1)) = interleave b (fun n => a (n + 1)) :=
  funext (interleave_succ a b)

/-- **Interleaving**, from the joined pairs to the shifted pairs. -/
theorem streamConcat_interleave_tail {a b : Nat → List α} {ω : Nat → α}
    (h : Shape.StreamConcat (fun n => a n ++ b n) ω) :
    ∃ ζ, ω = a 0 ++ₛ ζ ∧ Shape.StreamConcat (fun n => b n ++ a (n + 1)) ζ := by
  obtain ⟨he, ht⟩ := streamConcat_tail (streamConcat_interleave_iff.2 h)
  rw [interleave_shift, streamConcat_interleave_iff] at ht
  exact ⟨_, he, ht⟩

/-- **Interleaving**, from the shifted pairs to the joined pairs. -/
theorem streamConcat_interleave {a b : Nat → List α} {ζ : Nat → α}
    (h : Shape.StreamConcat (fun n => b n ++ a (n + 1)) ζ) :
    Shape.StreamConcat (fun n => a n ++ b n) (a 0 ++ₛ ζ) := by
  rw [← streamConcat_interleave_iff, ← interleave_shift] at h
  exact streamConcat_interleave_iff.1 (streamConcat_cons h)

end Silmaril.Proofs.Games.Abstract.FullFun
