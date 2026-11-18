module

public import Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv.Trace

/-!
# Explicit infinite runs from segments

* `irun_of_segs`: an infinite sequence of nonempty runs without host events, `c k` to
  `c (k + 1)`, is one explicit infinite run of internal steps (`IRun`) meeting every `c k` at a
  position at least `k`;
* `segs_compress`: a sequence of runs without host events, possibly empty, whose configurations
  change infinitely often, has a subsequence whose segments are nonempty, every configuration of
  the sequence being one of the subsequence.
-/

@[expose] public noncomputable section

namespace Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf

open Silmaril.Proofs.Wasm.Component.Reference
open Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionDiv
open Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Engine Silmaril.Wasm.Component.Runtime
  Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.Machine

variable {E : CoreEngine} {σ : Type} {prof : ProfileKind} {hr : HostReady σ}
  {dispatch : Call E → Canon.P E σ (Ret E)}

/-- One step of the run built from segments: along the current segment, counting down, or, at the
end of segment `k` (`c k`), into segment `k + 1`. -/
def SegStep (prof : ProfileKind) (hr : HostReady σ) (dispatch : Call E → Canon.P E σ (Ret E))
    (c : ℕ → Machine.Config E σ) (a b : Machine.Config E σ × ℕ × ℕ) : Prop :=
  InternalStep prof hr dispatch a.1 b.1 ∧
    ((a.2.2 = b.2.2 + 1 ∧ b.2.1 = a.2.1) ∨ (a.2.2 = 0 ∧ a.1 = c a.2.1 ∧ b.2.1 = a.2.1 + 1))

/-- **Nonempty segments are one explicit infinite run.** -/
theorem irun_of_segs {c : ℕ → Machine.Config E σ}
    (h : ∀ k, ∃ tr, Steps prof hr dispatch (c k) tr (c (k + 1)) ∧ tr ≠ [] ∧
      ∀ ev, Label.host ev ∉ tr) :
    ∃ t : ℕ → Machine.Config E σ, t 0 = c 0 ∧ IRun prof hr dispatch t ∧
      ∀ k, ∃ p, k ≤ p ∧ t p = c k := by
  let Q : Machine.Config E σ × ℕ × ℕ → Prop := fun a => ∃ tr,
    Steps prof hr dispatch a.1 tr (c a.2.1) ∧ tr.length = a.2.2 ∧ ∀ ev, Label.host ev ∉ tr
  have hstep : ∀ a, Q a → ∃ b, SegStep prof hr dispatch c a b ∧ Q b := by
    rintro ⟨m, k, d⟩ ⟨tr, r, hlen, hh⟩
    change Steps prof hr dispatch m tr (c k) at r
    generalize hck : c k = ck at r
    cases r with
    | refl =>
      obtain ⟨tr', r', hne, hh'⟩ := h k
      generalize hc0 : c k = c0 at r'
      generalize hc1 : c (k + 1) = c1 at r'
      cases r' with
      | refl => exact absurd rfl hne
      | @cons _ b _ l tr'' s r'' =>
        exact ⟨(b, k + 1, tr''.length),
          ⟨⟨l, fun ev e => hh' ev (e ▸ List.mem_cons_self), by rw [← hck, hc0]; exact s⟩,
            .inr ⟨by simpa using hlen.symm, hck.symm, rfl⟩⟩,
          tr'', by rw [← hc1] at r''; exact r'', rfl,
          fun ev hm => hh' ev (List.mem_cons_of_mem _ hm)⟩
    | @cons _ b _ l tr' s r' =>
      exact ⟨(b, k, tr'.length), ⟨⟨l, fun ev e => hh ev (e ▸ List.mem_cons_self), s⟩,
        .inl ⟨by simpa using hlen.symm, rfl⟩⟩, tr', by rw [← hck] at r'; exact r', rfl,
        fun ev hm => hh ev (List.mem_cons_of_mem _ hm)⟩
  obtain ⟨T, hT0, hT⟩ := Silmaril.InfiniteTrace.coinduct (R := SegStep prof hr dispatch c) Q hstep
    (a := (c 0, 0, 0)) ⟨[], .refl _, rfl, fun _ h => nomatch h⟩
  have hidx : ∀ n, (T n).2.1 ≤ n := by
    intro n
    induction n with
    | zero => rw [hT0]
    | succ n ih =>
      rcases (hT n).2 with ⟨-, e⟩ | ⟨-, -, e⟩ <;> omega
  have hdown : ∀ d n, (T n).2.2 = d → ∃ n', n ≤ n' ∧ (T n').2.2 = 0 ∧ (T n').2.1 = (T n).2.1 := by
    intro d
    induction d with
    | zero => exact fun n hn => ⟨n, le_rfl, hn, rfl⟩
    | succ d ih =>
      intro n hn
      rcases (hT n).2 with ⟨e₁, e₂⟩ | ⟨e, -⟩
      · obtain ⟨n', hn', h₁, h₂⟩ := ih (n + 1) (by omega)
        exact ⟨n', by omega, h₁, h₂.trans e₂⟩
      · omega
  have hreach : ∀ k, ∃ n, (T n).2.1 = k ∧ (T n).2.2 = 0 := by
    intro k
    induction k with
    | zero => exact ⟨0, by rw [hT0], by rw [hT0]⟩
    | succ k ih =>
      obtain ⟨n, hk, hd⟩ := ih
      rcases (hT n).2 with ⟨e, -⟩ | ⟨-, -, e⟩
      · omega
      · obtain ⟨n', -, h₁, h₂⟩ := hdown _ (n + 1) rfl
        exact ⟨n', h₂.trans (e.trans (congrArg (· + 1) hk)), h₁⟩
  refine ⟨fun n => (T n).1, by simp only [hT0], fun n => (hT n).1, fun k => ?_⟩
  obtain ⟨n, hk, hd⟩ := hreach k
  refine ⟨n, hk ▸ hidx n, ?_⟩
  rcases (hT n).2 with ⟨e, -⟩ | ⟨-, e, -⟩
  · omega
  · exact e.trans (congrArg c hk)

/-- **Segments changing infinitely often have a subsequence of nonempty segments** meeting every
configuration of the sequence. -/
theorem segs_compress {c : ℕ → Machine.Config E σ}
    (h : ∀ k, ∃ tr, Steps prof hr dispatch (c k) tr (c (k + 1)) ∧ ∀ ev, Label.host ev ∉ tr)
    (hinf : ∀ N, ∃ i, N ≤ i ∧ c i ≠ c (i + 1)) :
    ∃ φ : ℕ → ℕ, φ 0 = 0 ∧
      (∀ k, ∃ tr, Steps prof hr dispatch (c (φ k)) tr (c (φ (k + 1))) ∧ tr ≠ [] ∧
        ∀ ev, Label.host ev ∉ tr) ∧
      (∀ i, ∃ k, c i = c (φ k)) ∧ ∀ k, k ≤ φ k := by
  classical
  let nx : ℕ → ℕ := fun i => Nat.find (hinf i)
  have hnx : ∀ i, i ≤ nx i ∧ c (nx i) ≠ c (nx i + 1) := fun i => Nat.find_spec (hinf i)
  have hconst : ∀ i d, i + d ≤ nx i → c (i + d) = c i := by
    intro i d
    induction d with
    | zero => exact fun _ => rfl
    | succ d ih =>
      intro hd
      have hlt : i + d < nx i := by omega
      have hmin := Nat.find_min (hinf i) hlt
      have e : c (i + d) = c (i + d + 1) := by
        by_contra hne
        exact hmin ⟨by omega, hne⟩
      rw [← Nat.add_assoc, ← e]
      exact ih (by omega)
  let φ : ℕ → ℕ := fun k => Nat.rec 0 (fun _ p => nx p + 1) k
  have hφs : ∀ k, φ (k + 1) = nx (φ k) + 1 := fun _ => rfl
  have hφmono : ∀ k, k ≤ φ k := by
    intro k
    induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => rw [hφs]; have := (hnx (φ k)).1; omega
  refine ⟨φ, rfl, fun k => ?_, fun i => ?_, hφmono⟩
  · obtain ⟨tr, r, hh⟩ := h (nx (φ k))
    have e : c (nx (φ k)) = c (φ k) := by
      have := hconst (φ k) (nx (φ k) - φ k) (by have := (hnx (φ k)).1; omega)
      rwa [Nat.add_sub_cancel' (hnx (φ k)).1] at this
    refine ⟨tr, by rw [hφs, ← e]; exact r, ?_, hh⟩
    rintro rfl
    generalize hc0 : c (nx (φ k)) = c0 at r
    generalize hc1 : c (nx (φ k) + 1) = c1 at r
    cases r
    exact (hnx (φ k)).2 (hc0.trans hc1.symm)
  · have hex : ∃ k, i < φ (k + 1) := ⟨i, by have := hφmono (i + 1); omega⟩
    let k := Nat.find hex
    have hk : i < φ (k + 1) := Nat.find_spec hex
    have hk' : φ k ≤ i := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · rw [h0]
        exact Nat.zero_le _
      · obtain ⟨k', e⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
        have hmin := Nat.find_min hex (show k' < k by omega)
        rw [e]
        omega
    refine ⟨k, ?_⟩
    rw [hφs] at hk
    have := hconst (φ k) (i - φ k) (by omega)
    rwa [Nat.add_sub_cancel' hk'] at this

/-- **A finite run without host events, then an explicit infinite run**, is an explicit infinite
run. -/
theorem irun_prepend {m m' : Machine.Config E σ} {tr : List (Label E σ)}
    (r : Steps prof hr dispatch m tr m') (hh : ∀ ev, Label.host ev ∉ tr) :
    ∀ {t' : ℕ → Machine.Config E σ}, t' 0 = m' → IRun prof hr dispatch t' →
      ∃ t : ℕ → Machine.Config E σ, t 0 = m ∧ IRun prof hr dispatch t ∧
        ∀ p, t (tr.length + p) = t' p := by
  induction r with
  | refl => exact fun h0 ht => ⟨_, h0, ht, fun p => by simp⟩
  | @cons a b _ l tr s _ ih =>
    intro t' h0 ht
    obtain ⟨t₁, h₁0, h₁, hp⟩ := ih (fun ev hm => hh ev (List.mem_cons_of_mem _ hm)) h0 ht
    refine ⟨fun n => Nat.casesOn n a fun n => t₁ n, rfl, fun n => ?_, fun p => ?_⟩
    · cases n with
      | zero => exact ⟨l, fun ev e => hh ev (e ▸ List.mem_cons_self), by show Step prof hr dispatch a l (t₁ 0); rw [h₁0]; exact s⟩
      | succ n => exact h₁ n
    · show Nat.casesOn ((l :: tr).length + p) a (fun n => t₁ n) = t' p
      rw [List.length_cons, Nat.add_right_comm]
      exact hp p

end Silmaril.Proofs.Wasm.Component.Reference.HLinkedSessionInf
