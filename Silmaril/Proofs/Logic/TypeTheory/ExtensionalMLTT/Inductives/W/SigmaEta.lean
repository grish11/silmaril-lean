module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Derivation.Defs

@[expose] public section

namespace Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

open Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- Actual dependent-pair eta, with the original theory and universe budget. -/
theorem sigma_eta {levels : RuleBudget} {n : ℕ} {H : Set Jdg} {Γ : Ctx} {A q : Tm 0} {B : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hq : Γ.JEqB levels H (.sigma A B) q q) :
    Γ.JEqB levels H (.sigma A B) q (.pair (.fst q) (.snd q)) := by
  have hu : Γ.JEqB levels H A (.fst q) (.fst q) := .fst hn hA hB hq
  have hv : Γ.JEqB levels H (B.lst (.fst q)) (.snd q) (.snd q) := .snd hn hA hB hq
  have hp : Γ.JEqB levels H (.sigma A B) (.pair (.fst q) (.snd q)) (.pair (.fst q) (.snd q)) :=
    .pair hn hA hB hu hv
  exact .sigma_ext hn hA hB hq hp (Ctx.JEqB.beta_fst hn hA hB hu hv).symm (Ctx.JEqB.beta_snd hn hA hB hu hv).symm

end Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
