module

public import Silmaril.Logic.Temporal.LTL.NNF.Defs

@[expose] public section
namespace Silmaril.Logic.Temporal.LTL.NNF

theorem Formula.holds_dual {Atom : Type} (word : Nat → Atom → Prop)
    (p : Formula Atom) (n : Nat) : p.dual.Holds word n ↔ ¬ p.Holds word n := by
  classical
  induction p generalizing n with
  | pos a => rfl
  | neg a => simp [dual, Holds]
  | bot => simp [dual, Holds]
  | top => simp [dual, Holds]
  | conj p q hp hq => simp [dual, Holds, hp, hq, or_iff_not_imp_left]
  | disj p q hp hq => simp [dual, Holds, hp, hq]
  | next p hp => exact hp (n+1)
  | «until» p q hp hq => simp [dual, Holds, hp, hq, or_iff_not_imp_left]
  | release p q hp hq => simp [dual, Holds, hp, hq]

/-- Both polarities at every trace time, against existing independent LTL semantics. -/
theorem normalize_holds {Atom : Type} (M : LTL.Model Atom) (p : LTL.Formula Atom)
    (b : Bool) (n : Nat) :
    (normalize b p).Holds M.val n ↔ if b then ¬ p.Holds M n else p.Holds M n := by
  classical
  induction p generalizing b n with
  | atom a => cases b <;> rfl
  | bot => cases b <;> simp [normalize, Formula.Holds, LTL.Formula.Holds]
  | not p hp => cases b <;> simp [normalize, LTL.Formula.Holds, hp]
  | imp p q hp hq =>
    cases b
    · simp [normalize, Formula.Holds, LTL.Formula.Holds, hp, hq, or_iff_not_imp_left]
    · simp [normalize, Formula.Holds, LTL.Formula.Holds, hp, hq]
  | and p q hp hq =>
    cases b
    · simp [normalize, Formula.Holds, LTL.Formula.Holds, hp, hq]
    · simp [normalize, Formula.Holds, LTL.Formula.Holds, hp, hq, or_iff_not_imp_left]
  | or p q hp hq =>
    cases b <;> simp [normalize, Formula.Holds, LTL.Formula.Holds, hp, hq]
  | next p hp => cases b <;> simp [normalize, Formula.Holds, LTL.Formula.Holds, hp]
  | «until» p q hp hq =>
    cases b
    · simp [normalize, Formula.Holds, LTL.Formula.Holds, hp, hq]
    · simp [normalize, Formula.Holds, LTL.Formula.Holds, hp, hq, or_iff_not_imp_left]

theorem normalize_positive {Atom : Type} (M : LTL.Model Atom) (p : LTL.Formula Atom)
    (n : Nat) : (normalize false p).Holds M.val n ↔ p.Holds M n :=
  normalize_holds M p false n

theorem normalize_negative {Atom : Type} (M : LTL.Model Atom) (p : LTL.Formula Atom)
    (n : Nat) : (normalize true p).Holds M.val n ↔ ¬ p.Holds M n :=
  normalize_holds M p true n

end Silmaril.Logic.Temporal.LTL.NNF
