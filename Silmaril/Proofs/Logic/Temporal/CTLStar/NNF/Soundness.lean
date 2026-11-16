module

public import Silmaril.Logic.Temporal.CTLStar.NNF.Defs

@[expose] public section
namespace Silmaril.Logic.Temporal.CTLStar.NNF
open CategoryTheory

theorem Formula.holds_dual {A : Type} (last : Option Nat) (word : Nat → A → Prop)
    (p : Formula A) (i : Nat) : p.dual.Holds last word i ↔ ¬ p.Holds last word i := by
  classical
  induction p generalizing i with
  | pos a => rfl
  | neg a => simp [dual, Holds]
  | bot => simp [dual, Holds]
  | top => simp [dual, Holds]
  | conj p q hp hq => simp [dual, Holds, hp, hq, or_iff_not_imp_left]
  | disj p q hp hq => simp [dual, Holds, hp, hq]
  | strongNext p hp => simp [dual, Holds, hp]
  | weakNext p hp => simp [dual, Holds, hp]
  | «until» p q hp hq => simp [dual, Holds, hp, hq, or_iff_not_imp_left]
  | release p q hp hq => simp [dual, Holds, hp, hq]

private theorem holds_decode_all {A : Type} {S : Signature} (leaf : A → StateFormula S)
    (M : Model S) (path : Path M.toModal.accessible) (p : Formula A) (i : Nat) :
    p.Holds path.last (fun t a => (leaf a).Holds M (path.state t)) i ↔
      (p.toPathFormula leaf).Holds M path i := by
  classical
  induction p generalizing i with
  | pos a => rfl
  | neg a => rfl
  | bot => rfl
  | top => simp [Formula.Holds, Formula.toPathFormula, PathFormula.top,
      StateFormula.top, PathFormula.Holds, StateFormula.Holds]
  | conj p q hp hq => exact and_congr (hp i) (hq i)
  | disj p q hp hq =>
      simp [Formula.Holds, Formula.toPathFormula, PathFormula.Holds, hp, hq,
        or_iff_not_imp_left]
  | strongNext p hp => exact and_congr Iff.rfl (hp (i+1))
  | weakNext p hp =>
      rw [Formula.toPathFormula, PathFormula.weakNext_iff]
      exact imp_congr_right fun _ => hp (i+1)
  | «until» p q hp hq =>
      exact exists_congr fun d => and_congr_right fun _ => and_congr (hq (i+d))
        (forall_congr' fun j => imp_congr_right fun _ => hp (i+j))
  | release p q hp hq =>
      rw [Formula.toPathFormula, PathFormula.release_iff]
      exact forall_congr' fun d => imp_congr_right fun _ => or_congr (hq (i+d))
        (exists_congr fun j => and_congr_right fun _ => hp (i+j))

/-- At each genuine path position, direct bounded semantics agrees with existing CTL*. -/
theorem Formula.holds_toPathFormula {A : Type} {S : Signature} (leaf : A → StateFormula S)
    (M : Model S) (path : Path M.toModal.accessible) (p : Formula A) (i : Nat)
    (_hi : path.Valid i) :
    p.Holds path.last (fun t a => (leaf a).Holds M (path.state t)) i ↔
      (p.toPathFormula leaf).Holds M path i := holds_decode_all leaf M path p i

private theorem normalize_all {S : Signature} (M : Model S)
    (path : Path M.toModal.accessible) (p : PathFormula S) (b : Bool) (i : Nat) :
    (normalize b p).Holds path.last (fun t a => a.Holds M (path.state t)) i ↔
      if b then ¬ p.Holds M path i else p.Holds M path i := by
  classical
  cases p with
  | state p => cases b <;> rfl
  | neg p =>
      have hp := normalize_all M path p
      cases b <;> simp [normalize, PathFormula.Holds, hp]
  | conj p q =>
      have hp := normalize_all M path p
      have hq := normalize_all M path q
      cases b <;> simp [normalize, Formula.Holds, PathFormula.Holds, hp, hq,
        or_iff_not_imp_left]
  | next p =>
      have hp := normalize_all M path p
      cases b <;> simp [normalize, Formula.Holds, PathFormula.Holds, hp, Path.Valid]
  | «until» p q =>
      have hp := normalize_all M path p
      have hq := normalize_all M path q
      cases b <;> simp [normalize, Formula.Holds, PathFormula.Holds, hp, hq,
        Path.Valid, or_iff_not_imp_left]

/-- Both polarities preserve full CTL* path satisfaction at valid positions.
Nested state formulas remain interpreted by their existing semantics. -/
theorem normalize_holds {S : Signature} (M : Model S)
    (path : Path M.toModal.accessible) (p : PathFormula S) (b : Bool) (i : Nat)
    (_hi : path.Valid i) :
    (normalize b p).Holds path.last (fun t a => a.Holds M (path.state t)) i ↔
      if b then ¬ p.Holds M path i else p.Holds M path i := normalize_all M path p b i

theorem Formula.dual_dual {A : Type} (p : Formula A) : p.dual.dual = p := by
  induction p <;> simp_all [dual]

theorem Formula.dual_map {A B : Type} (f : A → B) (p : Formula A) :
    (p.map f).dual = p.dual.map f := by
  induction p <;> simp_all [map, dual]

theorem Formula.holds_map {A B : Type} (f : A → B) (last : Option Nat)
    (word : Nat → B → Prop) (p : Formula A) (i : Nat) :
    (p.map f).Holds last word i ↔ p.Holds last (fun t a => word t (f a)) i := by
  induction p generalizing i with
  | pos a => rfl
  | neg a => rfl
  | bot => rfl
  | top => rfl
  | conj p q hp hq => exact and_congr (hp i) (hq i)
  | disj p q hp hq => exact or_congr (hp i) (hq i)
  | strongNext p hp => exact and_congr Iff.rfl (hp (i+1))
  | weakNext p hp => exact imp_congr_right fun _ => hp (i+1)
  | «until» p q hp hq =>
      exact exists_congr fun d => and_congr_right fun _ => and_congr (hq (i+d))
        (forall_congr' fun j => imp_congr_right fun _ => hp (i+j))
  | release p q hp hq =>
      exact forall_congr' fun d => imp_congr_right fun _ => or_congr (hq (i+d))
        (exists_congr fun j => and_congr_right fun _ => hp (i+j))

/-- Actual normalization syntax commutes with arbitrary signature maps. -/
theorem normalize_map {S T : Signature} (f : S ⟶ T) (p : PathFormula S) (b : Bool) :
    normalize b (p.map f) = (normalize b p).map (fun q => q.map f) := by
  cases p with
  | state p => cases b <;> rfl
  | neg p =>
      have hp := normalize_map f p
      cases b <;> simp [normalize, PathFormula.map, hp]
  | conj p q =>
      have hp := normalize_map f p
      have hq := normalize_map f q
      cases b <;> simp [normalize, PathFormula.map, Formula.map, hp, hq]
  | next p =>
      have hp := normalize_map f p
      cases b <;> simp [normalize, PathFormula.map, Formula.map, hp]
  | «until» p q =>
      have hp := normalize_map f p
      have hq := normalize_map f q
      cases b <;> simp [normalize, PathFormula.map, Formula.map, hp, hq]

/-- Strong next cannot use a padded position beyond the finite endpoint. -/
theorem Formula.strongNext_at_last {A : Type} (word : Nat → A → Prop)
    (p : Formula A) (n : Nat) : ¬ p.strongNext.Holds (some n) word n := by
  rintro ⟨hv, _⟩
  change n+1 ≤ n at hv
  omega

theorem Formula.weakNext_at_last {A : Type} (word : Nat → A → Prop)
    (p : Formula A) (n : Nat) : p.weakNext.Holds (some n) word n := by
  intro hv
  change n+1 ≤ n at hv
  omega

/-- A finite Until obligation must discharge its right operand at the endpoint. -/
theorem Formula.until_at_last {A : Type} (word : Nat → A → Prop)
    (p q : Formula A) (n : Nat) :
    (p.until q).Holds (some n) word n ↔ q.Holds (some n) word n := by
  constructor
  · rintro ⟨d, hd, hq, _⟩
    have hz : d = 0 := by change n+d ≤ n at hd; omega
    simpa only [hz, Nat.add_zero] using hq
  · intro hq
    exact ⟨0, Nat.le_refl n, hq, fun j hj => (Nat.not_lt_zero j hj).elim⟩

theorem Formula.release_at_last {A : Type} (word : Nat → A → Prop)
    (p q : Formula A) (n : Nat) :
    (p.release q).Holds (some n) word n ↔ q.Holds (some n) word n := by
  constructor
  · intro h
    rcases h 0 (Nat.le_refl n) with hq | ⟨j, hj, _⟩
    · exact hq
    · exact (Nat.not_lt_zero j hj).elim
  · intro hq d hd
    have hz : d = 0 := by change n+d ≤ n at hd; omega
    exact Or.inl (by simpa only [hz, Nat.add_zero] using hq)

end Silmaril.Logic.Temporal.CTLStar.NNF
