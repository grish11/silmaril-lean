module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Derivation.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.SigmaEta

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem Ctx.JEqB.sigma_eta {levels : RuleBudget} {n : ℕ} {H : Set Jdg} {Γ : Ctx} {A q : Tm 0} {B : Tm 1}
    {L : Finset String} (hn : RuleBudget.Allows levels n)
    (hA : Γ.JEqB levels H (.univ n) A A)
    (hB : ∀ x ∉ L, (Γ.cons x A).JEqB levels H (.univ n) (B.open x) (B.open x))
    (hq : Γ.JEqB levels H (.sigma A B) q q) :
    Γ.JEqB levels H (.sigma A B) q (.pair (.fst q) (.snd q)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.sigma_eta hn hA hB hq

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
