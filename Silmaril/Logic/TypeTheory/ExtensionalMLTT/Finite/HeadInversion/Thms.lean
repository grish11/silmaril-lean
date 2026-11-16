module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.HeadInversion.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Regularity.Thms
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedHeadInversion

public section

/-!
# Same-budget head inversion of actual bounded extensional derivations

Every syntactic product or sum endpoint supplies actual bounded formation of
its components at a common universe index below the original level budget.
The proof preserves both endpoints through finite-support typed assignment,
including computation, reflection and changes to the newest declaration.
Every member of every cofinite family uses the same budget.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- An actual bounded syntactic product endpoint gives same-budget component formation. -/
theorem ECtx.JEqB.pi_formation {levels : ℕ} {Γ : ECtx} {A T v : ETm 0} {B : ETm 1}
    (h : ECtx.JEqB levels ∅ Γ T (.pi A B) v) :
    ∃ n : ℕ, n < levels ∧ ∃ L : Finset String, ECtx.JEqB levels ∅ Γ (.univ n) A A ∧ ∀ x ∉ L,
      ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedHeadInversion.pi_formation h

/-- An actual bounded syntactic sum endpoint gives same-budget component formation. -/
theorem ECtx.JEqB.sigma_formation {levels : ℕ} {Γ : ECtx} {A T v : ETm 0} {B : ETm 1}
    (h : ECtx.JEqB levels ∅ Γ T (.sigma A B) v) :
    ∃ n : ℕ, n < levels ∧ ∃ L : Finset String, ECtx.JEqB levels ∅ Γ (.univ n) A A ∧ ∀ x ∉ L,
      ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedHeadInversion.sigma_formation h

/-- An actual function typing supplies implicit component premises with one extra level. -/
theorem ECtx.JEqB.app_implicit {levels : ℕ} {Γ : ECtx} {A f f' a a' : ETm 0} {B : ETm 1}
    (hf : ECtx.JEqB levels ∅ Γ (.pi A B) f f') (ha : ECtx.JEqB levels ∅ Γ A a a') :
    ECtx.JEqB (levels + 1) ∅ Γ (B.lst a) (.app f a) (.app f' a') := by
  obtain ⟨n, hn, hPi⟩ := hf.type_formation
  obtain ⟨i, hi, L, hA, hB⟩ := hPi.pi_formation
  exact .app hi hA hB (hf.weakenLevels (Nat.le_succ levels)) (ha.weakenLevels (Nat.le_succ levels))

/-- An actual pair typing supplies implicit first-projection premises with one extra level. -/
theorem ECtx.JEqB.fst_implicit {levels : ℕ} {Γ : ECtx} {A p p' : ETm 0} {B : ETm 1}
    (hp : ECtx.JEqB levels ∅ Γ (.sigma A B) p p') :
    ECtx.JEqB (levels + 1) ∅ Γ A (.fst p) (.fst p') := by
  obtain ⟨n, hn, hSigma⟩ := hp.type_formation
  obtain ⟨i, hi, L, hA, hB⟩ := hSigma.sigma_formation
  exact .fst hi hA hB (hp.weakenLevels (Nat.le_succ levels))

/-- An actual pair typing supplies implicit dependent projection with one extra level. -/
theorem ECtx.JEqB.snd_implicit {levels : ℕ} {Γ : ECtx} {A p p' : ETm 0} {B : ETm 1}
    (hp : ECtx.JEqB levels ∅ Γ (.sigma A B) p p') :
    ECtx.JEqB (levels + 1) ∅ Γ (B.lst (.fst p)) (.snd p) (.snd p') := by
  obtain ⟨n, hn, hSigma⟩ := hp.type_formation
  obtain ⟨i, hi, L, hA, hB⟩ := hSigma.sigma_formation
  exact .snd hi hA hB (hp.weakenLevels (Nat.le_succ levels))

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
