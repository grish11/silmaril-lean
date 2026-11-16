module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Defs
public import Silmaril.Logic.Smt.Uflia.Quantified.Thms

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt
open Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
open Silmaril.Logic.Smt

private theorem holds_eq (v : Valuation) {k : Nat} {Γ : Fin k → Uflia.SortCode Empty}
    {s : Uflia.SortCode Empty}
    (values : ∀ i : Fin k, (target v).carriers.value (Γ i))
    (p q : Uflia.Quantified.Term signature Γ s) :
    Uflia.Quantified.Formula.Holds (Formula.eq p q) (target v) values ↔
      Uflia.Quantified.eval (Γ := Γ) (s := s) (target v) values p =
        Uflia.Quantified.eval (Γ := Γ) (s := s) (target v) values q := by
  classical
  change decide (Uflia.Quantified.eval (target v) values p =
    Uflia.Quantified.eval (target v) values q) = true ↔ _
  exact decide_eq_true_iff

private theorem holds_neg (v : Valuation) {k : Nat} {Γ : Fin k → Uflia.SortCode Empty}
    (values : ∀ i : Fin k, (target v).carriers.value (Γ i))
    (p : Uflia.Quantified.Formula signature Γ) :
    Uflia.Quantified.Formula.Holds (Formula.neg p) (target v) values ↔
      ¬ Uflia.Quantified.Formula.Holds p (target v) values := by
  change (!Uflia.Quantified.eval (target v) values p) = true ↔ _
  simp only [Bool.not_eq_true', Bool.eq_false_iff, Uflia.Quantified.Formula.Holds]

private theorem holds_conj (v : Valuation) {k : Nat} {Γ : Fin k → Uflia.SortCode Empty}
    (values : ∀ i : Fin k, (target v).carriers.value (Γ i))
    (p q : Uflia.Quantified.Formula signature Γ) :
    Uflia.Quantified.Formula.Holds (Formula.conj p q) (target v) values ↔
      Uflia.Quantified.Formula.Holds p (target v) values ∧
      Uflia.Quantified.Formula.Holds q (target v) values := by
  change (Uflia.Quantified.eval (target v) values p &&
    Uflia.Quantified.eval (target v) values q) = true ↔ _
  simp only [Bool.and_eq_true, Uflia.Quantified.Formula.Holds]

private theorem holds_disj (v : Valuation) {k : Nat} {Γ : Fin k → Uflia.SortCode Empty}
    (values : ∀ i : Fin k, (target v).carriers.value (Γ i))
    (p q : Uflia.Quantified.Formula signature Γ) :
    Uflia.Quantified.Formula.Holds (Formula.disj p q) (target v) values ↔
      Uflia.Quantified.Formula.Holds p (target v) values ∨
      Uflia.Quantified.Formula.Holds q (target v) values := by
  change (Uflia.Quantified.eval (target v) values p ||
    Uflia.Quantified.eval (target v) values q) = true ↔ _
  simp only [Bool.or_eq_true, Uflia.Quantified.Formula.Holds]

private theorem holds_ex (v : Valuation) {k : Nat} {Γ : Fin k → Uflia.SortCode Empty}
    (values : ∀ i : Fin k, (target v).carriers.value (Γ i)) (s : Uflia.SortCode Empty)
    (body : Uflia.Quantified.Formula signature (k := k + 1) (Fin.cases s Γ)) :
    Uflia.Quantified.Formula.Holds (.ex s body) (target v) values ↔
      ∃ x : (target v).carriers.value s, Uflia.Quantified.Formula.Holds body (target v) (Fin.cases x values) := by
  exact Uflia.Quantified.Formula.holds_ex s body (target v) values

/-- Every output term, source valuation and supported pattern is covered.
Hook witnesses range over the full standard carrier, not a literal enumeration. -/
theorem compile_correct {s : ValueSort} (p : Pattern s) (v : Valuation) :
    ∀ {k : Nat} {Γ : Fin k → Uflia.SortCode Empty}
      (values : ∀ i, (target v).carriers.value (Γ i))
      (out : Uflia.Quantified.Term signature Γ s.code),
    Uflia.Quantified.Formula.Holds (p.compile out) (target v) values ↔
      Uflia.Quantified.eval (target v) values out ∈ p.denote v := by
  classical
  induction p with
  | «variable» s name =>
      intros
      simp [Pattern.compile, Uflia.Quantified.Formula.Holds,
        Uflia.Quantified.eval, Uflia.Model.apply, target, Pattern.denote]
  | integer n =>
      intro k Γ values out
      change Uflia.Quantified.Formula.Holds (Formula.eq out (Formula.integer n))
        (target v) values ↔ Uflia.Quantified.eval (target v) values out = n
      rw [holds_eq]
      rfl
  | boolean b =>
      intro k Γ values out
      change Uflia.Quantified.Formula.Holds (Formula.eq out (Formula.boolean b))
        (target v) values ↔ Uflia.Quantified.eval (target v) values out = b
      rw [holds_eq]
      rfl
  | top s =>
      intro k Γ values out
      change true = true ↔ True
      simp
  | bottom s =>
      intro k Γ values out
      change false = true ↔ False
      simp
  | neg p ih =>
      intro k Γ values out
      change Uflia.Quantified.Formula.Holds (Formula.neg (p.compile out)) (target v) values ↔
        ¬ Uflia.Quantified.eval (target v) values out ∈ p.denote v
      rw [holds_neg]
      exact not_congr (ih values out)
  | conj p q ihp ihq =>
      intro k Γ values out
      change Uflia.Quantified.Formula.Holds (Formula.conj (p.compile out) (q.compile out))
        (target v) values ↔ _ ∧ _
      rw [holds_conj]
      exact and_congr (ihp values out) (ihq values out)
  | disj p q ihp ihq =>
      intro k Γ values out
      change Uflia.Quantified.Formula.Holds (Formula.disj (p.compile out) (q.compile out))
        (target v) values ↔ _ ∨ _
      rw [holds_disj]
      exact or_congr (ihp values out) (ihq values out)
  | intEq p q ihp ihq =>
      intro k Γ values out
      simp only [Pattern.compile, holds_ex, holds_conj, holds_eq, ihp, ihq]
      simp only [Uflia.Quantified.eval_weaken, Uflia.Quantified.eval,
        Formula.eq, Uflia.Model.apply, Fin.cases_zero, Fin.cases_succ]
      change (∃ x : Int, ∃ y : Int, x ∈ p.denote v ∧ y ∈ q.denote v ∧
        Uflia.Quantified.eval (target v) values out = decide (x = y)) ↔
        ∃ x ∈ p.denote v, ∃ y ∈ q.denote v,
          Uflia.Quantified.eval (target v) values out =
            Silmaril.Logic.Kore.Operational.Conditional.intEqual x y
      simp only [Silmaril.Logic.Kore.Operational.Conditional.intEqual]
      aesop
  | boolNot p ih =>
      intro k Γ values out
      simp only [Pattern.compile, holds_ex, holds_conj, holds_eq, ih]
      simp only [Uflia.Quantified.eval_weaken, Uflia.Quantified.eval,
        Formula.neg, Uflia.Model.apply, Fin.cases_zero]
      rfl

end Silmaril.Proofs.Logic.Kore.GeneralFixedPoint.Builtins.Smt
