module

public import Silmaril.Semantics.StreamMonitors.Defs
public import Silmaril.Semantics.Streams.Thms
public import Cslib.Computability.Languages.SafetyLiveness

/-! # Proofs: safety and liveness verdicts on chunk streams -/

@[expose] public section

namespace Silmaril.Proofs.Semantics.StreamMonitors

open Cslib Silmaril.Streams Filter

universe u

variable {α : Type u}

theorem mem_omegaLim_iff {L : Language α} {s : ωSequence α} :
    s ∈ L↗ω ↔ ∀ M, ∃ m, M ≤ m ∧ s.take m ∈ L := by
  rw [ωLanguage.mem_omegaLim, frequently_atTop]
  simp only [ωSequence.extract_eq_take]

theorem mem_safetyω {L : Language α} {s : ωSequence α} :
    s ∈ safetyω L ↔ ∀ n, s.take n ∈ L := Iff.rfl

theorem isSafety_safetyω (L : Language α) : (safetyω L).IsSafety := by
  rw [ωLanguage.isSafety_iff]
  intro xs hxs
  rw [mem_safetyω, not_forall] at hxs
  obtain ⟨n, hn⟩ := hxs
  refine ⟨n, fun ys hys => hn ?_⟩
  have := hys n
  have hle : n ≤ (xs.take n).length := by rw [ωSequence.length_take]
  rwa [ωSequence.take_append_of_le_length (h := hle), List.take_of_length_le (ωSequence.length_take n xs).le] at this

/-- On an infinite limit, the delivered prefixes are prefixes of the limit word. -/
theorem prefixAt_eq_take {cs : Chunks α} {s : ωSequence α} (h : cs.limit = .inf s) (n : ℕ) :
    cs.prefixAt n = s.take (cs.prefixAt n).length :=
  ((Chunks.limit_eq_iff.mp h).1 n).symm

theorem alwaysAt_of_mem_safetyω {L : Language α} {cs : Chunks α} {s : ωSequence α}
    (h : cs.limit = .inf s) (hs : s ∈ safetyω L) : cs.AlwaysAt L := fun n => by
  rw [prefixAt_eq_take h n]; exact hs _

theorem alwaysAt_ofω_iff {L : Language α} {s : ωSequence α} :
    (Chunks.ofω s).AlwaysAt L ↔ s ∈ safetyω L := by
  simp only [Chunks.AlwaysAt, Chunks.prefixAt_ofω]; rfl

/-- Coarse chunks can hide a violation: chunks `[a, a]` over `L` = even-length words. -/
theorem alwaysAt_coarse_counterexample :
    ∃ (L : Language Bool) (cs : Chunks Bool) (s : ωSequence Bool),
      cs.limit = .inf s ∧ cs.AlwaysAt L ∧ s ∉ safetyω L := by
  let L : Language Bool := {w | Even w.length}
  let cs : Chunks Bool := ωSequence.const [true, true]
  have hpre : ∀ n, cs.prefixAt n = List.replicate (2 * n) true := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Chunks.prefixAt_succ, ih]
      simp [cs, ωSequence.const, Nat.mul_succ, List.replicate_add]
  have htake : ∀ n, (ωSequence.const true).take n = List.replicate n true := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [ωSequence.take_succ', ih, List.replicate_succ']; rfl
  refine ⟨L, cs, ωSequence.const true, ?_, ?_, ?_⟩
  · refine Chunks.limit_eq_iff.mpr ⟨fun n => ?_, fun k => ⟨k, ?_⟩⟩
    · show (ωSequence.const true).take _ = _
      rw [hpre, List.length_replicate, htake]
    · rw [hpre, List.length_replicate]; omega
  · intro n
    show Even (cs.prefixAt n).length
    rw [hpre, List.length_replicate]; exact even_two_mul n
  · intro hs
    have : Even ((ωSequence.const true).take 1).length := hs 1
    rw [ωSequence.length_take] at this
    exact Nat.not_even_one this

/-- With progress, infinitely many yes answers witness the liveness property `L↗ω`. -/
theorem mem_omegaLim_of_infOftenAt {L : Language α} {cs : Chunks α} {s : ωSequence α}
    (h : cs.limit = .inf s) (hL : cs.InfOftenAt L) : s ∈ L↗ω := by
  rw [mem_omegaLim_iff]
  intro M
  obtain ⟨n₀, hn₀⟩ := (Chunks.limit_eq_iff.mp h).2 M
  obtain ⟨n, hn, hmem⟩ := hL n₀
  refine ⟨(cs.prefixAt n).length, hn₀.trans (cs.prefixAt_mono hn).length_le, ?_⟩
  rwa [← prefixAt_eq_take h]

theorem infOftenAt_ofω_iff {L : Language α} {s : ωSequence α} :
    (Chunks.ofω s).InfOftenAt L ↔ s ∈ L↗ω := by
  rw [mem_omegaLim_iff]; simp only [Chunks.InfOftenAt, Chunks.prefixAt_ofω]

/-- Without progress, every verdict is about the finite limit word. -/
theorem verdicts_of_limit_fin {L : Language α} {cs : Chunks α} {w : List α}
    (h : cs.limit = .fin w) :
    (cs.InfOftenAt L ↔ w ∈ L) ∧ (cs.EventuallyAlwaysAt L ↔ w ∈ L) := by
  obtain ⟨N, hN⟩ := Chunks.limit_eq_iff.mp h
  refine ⟨⟨fun hL => ?_, fun hw M => ⟨max M N, le_max_left _ _, ?_⟩⟩,
    ⟨fun ⟨M, hM⟩ => ?_, fun hw => ⟨N, fun n hn => ?_⟩⟩⟩
  · obtain ⟨n, hn, hmem⟩ := hL N
    rwa [hN n hn] at hmem
  · rw [hN _ (le_max_right _ _)]; exact hw
  · have := hM (max M N) (le_max_left _ _)
    rwa [hN _ (le_max_right _ _)] at this
  · rw [hN n hn]; exact hw

/-! ## Liveness of `L↗ω` -/

/-- If every word extends by a nonempty word into `L`, then `L↗ω` is a liveness property. -/
theorem isLiveness_omegaLim {L : Language α} (hL : ∀ u, ∃ v, v ≠ [] ∧ u ++ v ∈ L) :
    (L↗ω).IsLiveness := by
  rw [ωLanguage.isLiveness_iff]
  intro xs n
  let ext : List α → List α := fun u => Classical.choose (hL u)
  have hext : ∀ u, ext u ≠ [] ∧ u ++ ext u ∈ L := fun u => Classical.choose_spec (hL u)
  let pre : ℕ → List α := fun k => Nat.rec (xs.take n) (fun _ p => p ++ ext p) k
  let cs : Chunks α := fun k => match k with
    | 0 => xs.take n
    | k + 1 => ext (pre k)
  have hpre : ∀ k, cs.prefixAt (k + 1) = pre k := by
    intro k
    induction k with
    | zero => rw [Chunks.prefixAt_succ]; rfl
    | succ k ih => rw [Chunks.prefixAt_succ, ih]; rfl
  have hprog : cs.Progressive := fun N => ⟨N + 1, Nat.le_succ N, (hext _).1⟩
  have hinf := (Chunks.isInfinite_limit_iff cs).mpr hprog
  cases hlim : cs.limit with
  | fin w => rw [hlim] at hinf; exact absurd trivial hinf
  | inf s =>
    have hfirst : s.take (xs.take n).length = xs.take n := by
      have := prefixAt_eq_take hlim 1
      rw [hpre 0] at this
      exact this.symm
    refine ⟨s.drop n, ?_⟩
    have hs : xs.take n ++ω s.drop n = s := by
      have := ωSequence.append_take_drop n s
      rwa [← ωSequence.length_take n xs, hfirst, ωSequence.length_take] at this
    rw [hs]
    apply mem_omegaLim_of_infOftenAt hlim
    intro N
    refine ⟨N + 2, by omega, ?_⟩
    rw [hpre]
    exact (hext _).2

end Silmaril.Proofs.Semantics.StreamMonitors
