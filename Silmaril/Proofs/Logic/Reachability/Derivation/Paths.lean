module

public import Silmaril.Logic.Reachability.Derivation.Defs

@[expose] public section
namespace Silmaril.Logic.Reachability.Derivation

variable {J W : Type} {D : J → Type} {R : W → W → Prop}

/-- A suffix of a complete path is complete, with the same final state. -/
def CompletePath.suffix (p : CompletePath R) (i : Nat) (hi : i ≤ p.length) : CompletePath R where
  length := p.length - i
  point := fun j => p.point (i + j)
  edge := by
    intro j hj
    have bound : i + j < p.length := by omega
    simpa only [Nat.add_assoc] using p.edge (i + j) bound
  terminal := by
    have last : i + (p.length - i) = p.length := by omega
    simpa only [last] using p.terminal

theorem Bounded.mono {δ : Bool} {n k : Nat} {c : Claim D W}
    (h : Bounded R δ n c) (hk : k ≤ n) : Bounded R δ k c :=
  fun a p hp hw => h a p (Nat.le_trans hp hk) hw

theorem Bounded.weaken {n : Nat} {c : Claim D W}
    (h : Bounded R true n c) : Bounded R false n c := by
  intro a p hp hw
  obtain ⟨i, hi, hq, _⟩ := h a p hp hw
  exact ⟨i, hi, hq, by simp⟩

theorem Bounded.zero (δ : Bool) (c : Claim D W) : Bounded R δ 0 c := by
  intro a p hp hw
  omega

theorem Environment.mono {δ : Bool} {n k : Nat} {E : Set (Claim D W)}
    (h : Environment R δ n E) (hk : k ≤ n) : Environment R δ k E :=
  fun c hc => (h c hc).mono hk

theorem Environment.empty (δ : Bool) (n : Nat) :
    Environment R δ n (∅ : Set (Claim D W)) := by
  intro c hc
  exact False.elim hc

theorem Environment.union {δ : Bool} {n : Nat} {A C : Set (Claim D W)}
    (hA : Environment R δ n A) (hC : Environment R δ n C) :
    Environment R δ n (A ∪ C) := by
  intro c hc
  exact hc.elim (hA c) (hC c)

/-- Shift a suffix hit back into the original complete path. -/
theorem Hit.shift {δ : Bool} {Q : W → Prop} (p : CompletePath R)
    {i : Nat} (hi : i ≤ p.length) (h : Hit δ Q (p.suffix i hi)) :
    Hit δ Q p := by
  obtain ⟨j, hj, hq, hpos⟩ := h
  refine ⟨i + j, ?_, hq, ?_⟩
  · change j ≤ p.length - i at hj
    omega
  · intro flag
    have := hpos flag
    omega

/-- A positive prefix followed by even an immediate suffix hit is positive. -/
theorem Hit.shift_positive {Q : W → Prop} (p : CompletePath R)
    {i : Nat} (hi : i ≤ p.length) (positive : 0 < i)
    (h : Hit false Q (p.suffix i hi)) : Hit true Q p := by
  obtain ⟨j, hj, hq, _⟩ := h
  refine ⟨i + j, ?_, hq, ?_⟩
  · change j ≤ p.length - i at hj
    omega
  · intro _
    omega

theorem bounded_all_iff (c : Claim D W) :
    (∀ n, Bounded R false n c) ↔ ∀ a w, c.pre a w → AllPartial R (c.post a) w := by
  constructor
  · intro h a w hw m path h0 edges terminal
    let p : CompletePath R := ⟨m, path, edges, terminal⟩
    obtain ⟨i, hi, hq, _⟩ := h (m + 1) a p (Nat.le_refl _) (by change c.pre a (path 0); rw [h0]; exact hw)
    exact ⟨i, hi, hq⟩
  · intro h n a p hp hw
    obtain ⟨i, hi, hq⟩ := h a (p.point 0) hw p.length p.point rfl p.edge p.terminal
    exact ⟨i, hi, hq, by simp⟩

end Silmaril.Logic.Reachability.Derivation
