module

public import Silmaril.Logic.TypeTheory.IntensionalMLTT.Rules.Defs

@[expose] public section

/-!
# Whole-derivation universe budgets

Unlike a bound on the final judgment, these budgets recursively include every
premise and conversion intermediate. Derivations are finite proof data in
`Type`, allowing the budget to be computed without elimination from `Prop`.
-/

namespace Silmaril.Logic.TypeTheory.IntensionalMLTT

/-- Largest universe occurrence across every node of a conversion tree, plus one. -/
def Conversion.universeBudget : {n : ℕ} → {t u : Term n} → Conversion t u → ℕ
  | _, t, u, h => max (max t.universeBound u.universeBound) (match h with
    | .refl _ => 0
    | .symm h => h.universeBudget
    | .trans h k => max h.universeBudget k.universeBudget
    | .beta _ _ _ | .fst_pair _ _ | .snd_pair _ _ | .nat_zero _ _ _ |
        .nat_succ _ _ _ _ | .j_refl _ _ _ _ => 0
    | .congr_succ h | .congr_fst h | .congr_snd h | .congr_refl h => h.universeBudget
    | .congr_pi h k | .congr_sigma h k | .congr_lam h k | .congr_app h k |
        .congr_pair h k | .congr_absurd h k => max h.universeBudget k.universeBudget
    | .congr_natrec h k l m =>
        max (max h.universeBudget k.universeBudget) (max l.universeBudget m.universeBudget)
    | .congr_id h k l => max h.universeBudget (max k.universeBudget l.universeBudget)
    | .congr_j h k l m p q => max (max h.universeBudget k.universeBudget)
        (max (max l.universeBudget m.universeBudget) (max p.universeBudget q.universeBudget)))

mutual

/-- Budget of every declaration's typing proof, including all its premises. -/
def ContextDerivation.universeBudget : {n : ℕ} → {Γ : Context n} → ContextDerivation Γ → ℕ
  | _, _, .nil => 0
  | _, _, .snoc hΓ hA => max hΓ.universeBudget hA.universeBudget

/-- A whole-proof budget including context, endpoints, rules and conversions. -/
def Derivation.universeBudget : {n : ℕ} → {Γ : Context n} → {t A : Term n} →
    Derivation Γ t A → ℕ
  | _, Γ, t, A, h => max (max Γ.universeBound (max t.universeBound A.universeBound))
      (match h with
    | .univ hΓ _ | .nat hΓ | .empty hΓ | .unit hΓ | .var hΓ _ |
        .zero hΓ | .star hΓ => hΓ.universeBudget
    | .pi h k | .sigma h k | .app h k | .absurd h k | .refl h k =>
        max h.universeBudget k.universeBudget
    | .lam h k l | .id h k l => max h.universeBudget (max k.universeBudget l.universeBudget)
    | .pair h k l m | .natrec h k l m =>
        max (max h.universeBudget k.universeBudget) (max l.universeBudget m.universeBudget)
    | .fst h | .snd h | .succ h | .cumulative h _ => h.universeBudget
    | .j h k l m p q => max (max h.universeBudget k.universeBudget)
        (max (max l.universeBudget m.universeBudget) (max p.universeBudget q.universeBudget))
    | .conv h k c => max h.universeBudget (max k.universeBudget c.universeBudget))

end

/-- Actual derivation data whose whole-proof universe budget fits the given count. -/
abbrev BoundedDerivation (levels : ℕ) {n : ℕ} (Γ : Context n) (t A : Term n) :=
  {d : Derivation Γ t A // d.universeBudget ≤ levels}

/-- Include a bounded proof into a larger universe budget without changing its tree. -/
def BoundedDerivation.include {levels more n : ℕ} {Γ : Context n} {t A : Term n}
    (h : levels ≤ more) (d : BoundedDerivation levels Γ t A) : BoundedDerivation more Γ t A :=
  ⟨d.val, d.property.trans h⟩

end Silmaril.Logic.TypeTheory.IntensionalMLTT
