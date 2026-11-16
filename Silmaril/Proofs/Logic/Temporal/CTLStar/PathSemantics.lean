module

public import Silmaril.Logic.Temporal.CTLStar.Path.Thms

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar

namespace PathFormula
variable {S : Signature} (M : Model S)

/-- At a valid position, satisfaction does not inspect finite-path padding. -/
theorem holds_congr (p : PathFormula S) (path other : Path M.toModal.accessible)
    (hlast : path.last = other.last)
    (hstate : ∀ j, path.Valid j → path.state j = other.state j)
    (i : Nat) (hi : path.Valid i) : p.Holds M path i ↔ p.Holds M other i := by
  have hv (j : Nat) : path.Valid j ↔ other.Valid j := by unfold Path.Valid; rw [hlast]
  cases p with
  | state p =>
    change p.Holds M (path.state i) ↔ p.Holds M (other.state i)
    rw [hstate i hi]
  | neg p => exact not_congr (p.holds_congr path other hlast hstate i hi)
  | conj p q =>
    exact and_congr (p.holds_congr path other hlast hstate i hi)
      (q.holds_congr path other hlast hstate i hi)
  | next p =>
    exact (and_congr_right fun hj => p.holds_congr path other hlast hstate (i+1) hj).trans
      (and_congr (hv (i+1)) Iff.rfl)
  | «until» p q =>
    apply exists_congr
    intro d
    apply Iff.trans (and_congr_right fun hd => ?_) (and_congr (hv (i+d)) Iff.rfl)
    exact and_congr (q.holds_congr path other hlast hstate (i+d) hd)
      (forall_congr' fun j => imp_congr_right fun hj =>
        p.holds_congr path other hlast hstate (i+j) (path.valid_of_le hd (by omega)))

/-- Suffix semantics agrees at every index; its states are reindexed exactly. -/
theorem holds_suffix (p : PathFormula S) (path : Path M.toModal.accessible)
    (k : Nat) (hk : path.Valid k) (i : Nat) :
    p.Holds M (path.suffix k hk) i ↔ p.Holds M path (k+i) := by
  cases p with
  | state p => rfl
  | neg p => exact not_congr (p.holds_suffix path k hk i)
  | conj p q => exact and_congr (p.holds_suffix path k hk i) (q.holds_suffix path k hk i)
  | next p =>
    simpa only [Holds, Nat.add_assoc] using and_congr (path.suffix_valid k hk (i+1))
      (p.holds_suffix path k hk (i+1))
  | «until» p q =>
    change (∃ d, (path.suffix k hk).Valid (i+d) ∧ _ ∧ _) ↔ _
    apply exists_congr
    intro d
    simpa only [Nat.add_assoc] using and_congr (path.suffix_valid k hk (i+d))
      (and_congr (q.holds_suffix path k hk (i+d))
        (forall_congr' fun j => imp_congr_right fun _ => p.holds_suffix path k hk (i+j)))

/-- Under seriality the infiniteness guard is redundant on every maximal path. -/
theorem infinite_of_serial (path : Path M.toModal.accessible)
    (serial : ∀ w, ∃ v, M.toModal.accessible w v) : PathFormula.infinite.Holds M path 0 :=
  (infinite_iff M path).mpr (path.last_none_of_serial serial)

end PathFormula

/-- Serial frames recover the conventional unguarded translation of CTL EG. -/
theorem ctl_eg_serial {S : Signature} (M : Model S) (p : CTL.Formula S)
    (serial : ∀ w, ∃ v, M.toModal.accessible w v) (w : M.toModal.World) :
    (StateFormula.existsPath (.globally (.state (encodeCTL p)))).Holds M w ↔
      (encodeCTL (.eg p)).Holds M w := by
  constructor
  · rintro ⟨path, h0, hp⟩
    exact ⟨path, h0, hp, PathFormula.infinite_of_serial M path serial⟩
  · rintro ⟨path, h0, hp, _⟩
    exact ⟨path, h0, hp⟩

theorem StateFormula.allPaths_iff {S : Signature} (M : Model S) (p : PathFormula S)
    (w : M.toModal.World) : (StateFormula.allPaths p).Holds M w ↔
      ∀ path : Path M.toModal.accessible, path.state 0 = w → p.Holds M path 0 := by
  classical
  simp only [StateFormula.allPaths, StateFormula.Holds, PathFormula.Holds,
    not_exists, not_and, not_not]

theorem allUntil_iff_maximal {W : Type} (R : W → W → Prop) (P Q : W → Prop) (w : W) :
    CTL.AllUntil R P Q w ↔ ∀ path : Path R, path.state 0 = w →
      ∃ n, path.Valid n ∧ Q (path.state n) ∧ ∀ i, i < n → P (path.state i) := by
  constructor
  · show CTL.AllUntil R P Q w → _
    intro h path h0
    show ∃ n, path.Valid n ∧ Q (path.state n) ∧ ∀ i, i < n → P (path.state i)
    cases he : path.last with
    | none =>
      obtain ⟨n, hq, hp⟩ := h.1 path.state h0
        (fun i => path.edges i (by simp only [ValidIndex, he]))
      exact ⟨n, by simp only [Path.Valid, ValidIndex, he], hq, hp⟩
    | some m =>
      obtain ⟨n, hn, hq, hp⟩ := h.2 m path.state h0
        (fun i hi => path.edges i (by simp only [ValidIndex, he]; omega)) (path.terminal m he)
      exact ⟨n, by simpa only [Path.Valid, ValidIndex, he] using hn, hq, hp⟩
  · show _ → CTL.AllUntil R P Q w
    intro h
    show CTL.AllUntil R P Q w
    constructor
    · intro seq h0 he
      let path : Path R := ⟨seq, none, fun n _ => he n, fun _ hn => by cases hn⟩
      obtain ⟨n, _, hq, hp⟩ := h path h0
      exact ⟨n, hq, hp⟩
    · intro m seq h0 he ht
      let path : Path R := ⟨seq, some m,
        fun i hi => he i (by dsimp only [ValidIndex] at hi; omega),
        fun n hn => by cases Option.some.inj hn; exact ht⟩
      obtain ⟨n, hn, hq, hp⟩ := h path h0
      exact ⟨n, hn, hq, hp⟩

/-- Universal strong until quantifies both infinite and terminal finite paths. -/
theorem StateFormula.all_until_iff {S : Signature} (M : Model S)
    (p q : StateFormula S) (w : M.toModal.World) :
    (StateFormula.allPaths (.until (.state p) (.state q))).Holds M w ↔
      CTL.AllUntil M.toModal.accessible (p.Holds M) (q.Holds M) w := by
  rw [StateFormula.allPaths_iff, allUntil_iff_maximal]
  simp only [PathFormula.Holds, Nat.zero_add]

/-- Strong universal until requires its right operand now at a deadlock. -/
theorem StateFormula.all_until_deadlock {S : Signature} (M : Model S)
    (p q : StateFormula S) (w : M.toModal.World)
    (hdead : ∀ v, ¬ M.toModal.accessible w v) :
    (StateFormula.allPaths (.until (.state p) (.state q))).Holds M w ↔ q.Holds M w := by
  rw [StateFormula.all_until_iff]
  constructor
  · intro h
    obtain ⟨i, hi, hq, _⟩ := h.2 0 (fun _ => w) rfl
      (fun _ hi => (Nat.not_lt_zero _ hi).elim) hdead
    exact hq
  · intro hq
    constructor
    · intro seq h0 he
      exact (hdead (seq 1) (h0 ▸ he 0)).elim
    · intro n seq h0 _ _
      exact ⟨0, Nat.zero_le n, h0.symm ▸ hq, fun _ hi => (Nat.not_lt_zero _ hi).elim⟩

end Silmaril.Logic.Temporal.CTLStar
