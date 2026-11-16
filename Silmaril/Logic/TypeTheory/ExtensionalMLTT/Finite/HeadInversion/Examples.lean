module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.HeadInversion.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation.Examples

public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

private theorem lastCases_zero {α : Sort _} (a : α) (f : Fin 0 → α) :
    Fin.lastCases a f (0 : Fin 1) = a := Fin.lastCases_last

private theorem nats_family : ∀ x ∉ (∅ : Finset String),
    ECtx.JEqB 1 ∅ (.cons .nil x .nats) (.univ 0)
      ((.nats : ETm 1).open x) ((.nats : ETm 1).open x) := by
  intro x hx
  simpa only [ETm.open] using ECtx.JEqB.nats (n := 0) (by decide) (bounded_nats_context x)

private theorem beta_type {t : ETm 0} (ht : ECtx.JEqB 2 ∅ .nil (.univ 0) t t) :
    ECtx.JEqB 2 ∅ .nil (.univ 0) (.app (.abs (.univ 0) (.bv 0)) t) t := by
  have hctx (x : String) : ECtx.JEqB 2 ∅ (.cons .nil x (.univ 0)) .unit .star .star :=
    .cons_ok (by decide) .nil_ok (by simp [ECtx.dv]) bounded_univ_zero
  have hU : ∀ x ∉ (∅ : Finset String), ECtx.JEqB 2 ∅ (.cons .nil x (.univ 0)) (.univ 1)
      ((.univ 0 : ETm 1).open x) ((.univ 0 : ETm 1).open x) := by
    intro x hx
    simpa only [ETm.open] using ECtx.JEqB.univ (n := 0) (by decide) (hctx x)
  have hBody : ∀ x ∉ (∅ : Finset String), ECtx.JEqB 2 ∅ (.cons .nil x (.univ 0))
      ((.univ 0 : ETm 1).open x) ((.bv 0 : ETm 1).open x) ((.bv 0 : ETm 1).open x) := by
    intro x hx
    simpa only [ETm.open, lastCases_zero] using ECtx.JEqB.var (hctx x) (.here _ _ _)
  simpa only [ETm.lst, lastCases_zero, ETm.castLE_refl] using
    ECtx.JEqB.beta_app (by decide) bounded_univ_zero hU hBody ht

/-- A product reached by actual beta contraction retains same-budget components. -/
theorem bounded_beta_pi_components : ∃ n : ℕ, n < 2 ∧ ∃ L : Finset String,
    ECtx.JEqB 2 ∅ .nil (.univ n) .nats .nats ∧ ∀ x ∉ L,
      ECtx.JEqB 2 ∅ (.cons .nil x .nats) (.univ n)
        ((.nats : ETm 1).open x) ((.nats : ETm 1).open x) := by
  have hPi : ECtx.JEqB 1 ∅ .nil (.univ 0) (.pi .nats .nats) (.pi .nats .nats) :=
    .pi (by decide) bounded_nats nats_family
  exact (ECtx.JEqB.symm (beta_type (hPi.weakenLevels (by decide)))).pi_formation

/-- A sum reached by actual beta contraction retains same-budget components. -/
theorem bounded_beta_sigma_components : ∃ n : ℕ, n < 2 ∧ ∃ L : Finset String,
    ECtx.JEqB 2 ∅ .nil (.univ n) .nats .nats ∧ ∀ x ∉ L,
      ECtx.JEqB 2 ∅ (.cons .nil x .nats) (.univ n)
        ((.nats : ETm 1).open x) ((.nats : ETm 1).open x) := by
  have hSigma : ECtx.JEqB 1 ∅ .nil (.univ 0) (.sigma .nats .nats) (.sigma .nats .nats) :=
    .sigma (by decide) bounded_nats nats_family
  exact (ECtx.JEqB.symm (beta_type (hSigma.weakenLevels (by decide)))).sigma_formation

/-- Actual function typing suffices for application when component formation is implicit. -/
theorem bounded_implicit_identity_application :
    ECtx.JEqB 2 ∅ .nil .nats
      (.app (.abs .nats (.bv 0)) .zero) (.app (.abs .nats (.bv 0)) .zero) := by
  have hb : ∀ x ∉ (∅ : Finset String), ECtx.JEqB 1 ∅ (.cons .nil x .nats)
      ((.nats : ETm 1).open x) ((.bv 0 : ETm 1).open x) ((.bv 0 : ETm 1).open x) := by
    intro x hx
    simpa only [ETm.open, lastCases_zero] using ECtx.JEqB.var (bounded_nats_context x) (.here _ _ _)
  have hf : ECtx.JEqB 1 ∅ .nil (.pi .nats .nats) (.abs .nats (.bv 0)) (.abs .nats (.bv 0)) :=
    .abs (by decide) bounded_nats nats_family hb
  simpa only [ETm.lst] using hf.app_implicit (.zero .nil_ok)

/-- Actual pair typing supplies both implicit projections at the next budget. -/
theorem bounded_implicit_pair_projections :
    ECtx.JEqB 2 ∅ .nil .nats (.fst (.pair .zero .zero)) (.fst (.pair .zero .zero)) ∧
      ECtx.JEqB 2 ∅ .nil .nats (.snd (.pair .zero .zero)) (.snd (.pair .zero .zero)) := by
  have hp : ECtx.JEqB 1 ∅ .nil (.sigma .nats .nats) (.pair .zero .zero) (.pair .zero .zero) := by
    apply ECtx.JEqB.pair (n := 0) (by decide) bounded_nats nats_family (.zero .nil_ok)
    simpa only [ETm.lst] using ECtx.JEqB.zero (levels := 1) (H := ∅) .nil_ok
  exact ⟨hp.fst_implicit, by simpa only [ETm.lst] using hp.snd_implicit⟩

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
