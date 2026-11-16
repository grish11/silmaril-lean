module

public import Silmaril.Logic.Temporal.CTLStar.Defs

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar

namespace Path
variable {W : Type} {R : W → W → Prop}

theorem valid_zero (p : Path R) : p.Valid 0 := by
  cases h : p.last <;> simp [Valid, ValidIndex, h]

theorem valid_of_le (p : Path R) {i j : Nat} (h : p.Valid j) (hij : i ≤ j) : p.Valid i := by
  cases he : p.last with
  | none => simp only [Valid, ValidIndex, he]
  | some n =>
    have hj : j ≤ n := by simpa only [Valid, ValidIndex, he] using h
    simpa only [Valid, ValidIndex, he] using Nat.le_trans hij hj

/-- Every finite actual prefix has a maximal extension, without seriality. -/
theorem maximal_extension (n : Nat) (seq : Nat → W)
    (edges : ∀ i, i < n → R (seq i) (seq (i+1))) :
    ∃ p : Path R, (∀ i, i ≤ n → p.state i = seq i) ∧ p.Valid n := by
  obtain ⟨ext, hp, hi | ⟨m, hnm, he, ht⟩⟩ :=
    CTL.finite_prefix_maximal_extension R n seq edges
  · exact ⟨⟨ext, none, fun i _ => hi i, fun _ h => by cases h⟩, hp, trivial⟩
  · refine ⟨⟨ext, some m, fun i hi => he i (by dsimp only [ValidIndex] at hi; omega), ?_⟩, hp, hnm⟩
    intro k hk
    cases Option.some.inj hk
    exact ht

theorem exists_from (w : W) : ∃ p : Path R, p.state 0 = w := by
  obtain ⟨p, hp, _⟩ := maximal_extension 0 (fun _ => w) (fun _ h => (Nat.not_lt_zero _ h).elim)
  exact ⟨p, hp 0 le_rfl⟩

/-- Seriality rules out finite maximal paths; no transitions are inserted. -/
theorem last_none_of_serial (p : Path R) (serial : ∀ w, ∃ v, R w v) : p.last = none := by
  cases h : p.last with
  | none => rfl
  | some n =>
    obtain ⟨v, hv⟩ := serial (p.state n)
    exact (p.terminal n h v hv).elim

/-- The suffix of an actual maximal path at a valid position. -/
def suffix (p : Path R) (k : Nat) (hk : p.Valid k) : Path R where
  state i := p.state (k+i)
  last := p.last.map (fun n => n-k)
  edges := by
    intro i hi
    have hvalid : p.Valid (k+i+1) := by
      cases h : p.last with
      | none => simp only [Valid, ValidIndex, h]
      | some n =>
        have hk' : k ≤ n := by simpa only [Valid, ValidIndex, h] using hk
        have hi' : i+1 ≤ n-k := by simpa only [h, Option.map_some, ValidIndex] using hi
        simp only [Valid, ValidIndex, h]
        omega
    simpa only [Nat.add_assoc] using p.edges (k+i) hvalid
  terminal := by
    intro n hn v hv
    cases h : p.last with
    | none => simp only [h, Option.map_none] at hn; cases hn
    | some m =>
      have hk' : k ≤ m := by simpa only [Valid, ValidIndex, h] using hk
      have hn' : m-k = n := by simpa only [h, Option.map_some, Option.some.injEq] using hn
      have he : k+n = m := by omega
      exact p.terminal m h v (he ▸ hv)

theorem suffix_valid (p : Path R) (k : Nat) (hk : p.Valid k) (i : Nat) :
    (p.suffix k hk).Valid i ↔ p.Valid (k+i) := by
  cases h : p.last with
  | none => simp only [Valid, suffix, h, Option.map_none, ValidIndex]
  | some n =>
    have hk' : k ≤ n := by simpa only [Valid, ValidIndex, h] using hk
    simp only [Valid, ValidIndex, suffix, h, Option.map_some]
    omega

end Path

namespace PathFormula
variable {S : Signature} (M : Model S)

theorem globally_iff (p : PathFormula S) (path : Path M.toModal.accessible) (i : Nat) :
    p.globally.Holds M path i ↔ ∀ d, path.Valid (i+d) → p.Holds M path (i+d) := by
  classical
  change (¬ ∃ d, path.Valid (i+d) ∧ ¬ p.Holds M path (i+d) ∧
    ∀ j, j < d → ¬ False) ↔ _
  constructor
  · intro h d hd
    by_contra hp
    exact h ⟨d, hd, hp, fun _ _ => not_false⟩
  · intro h ⟨d, hd, hn, _⟩
    exact hn (h d hd)

theorem infinite_iff (path : Path M.toModal.accessible) :
    PathFormula.infinite.Holds M path 0 ↔ path.last = none := by
  classical
  rw [infinite, globally_iff]
  constructor
  · intro h
    cases he : path.last with
    | none => rfl
    | some n =>
      have hn : path.Valid (0+n) := by simp [Path.Valid, ValidIndex, he]
      have hn' := (h n hn).1
      simp only [Path.Valid, ValidIndex, he, Nat.zero_add] at hn'
      omega
  · intro he d _
    exact ⟨by simp [Path.Valid, ValidIndex, he], by exact not_false⟩

end PathFormula
end Silmaril.Logic.Temporal.CTLStar
