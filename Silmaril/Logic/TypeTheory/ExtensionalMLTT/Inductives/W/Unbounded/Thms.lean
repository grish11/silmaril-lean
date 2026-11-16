module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Finite.Derivation.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.RuleBudget.Thms
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.UnboundedDerivation

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

/-- Every original rule, including its entire cofinite premise family, has unrestricted budget. -/
theorem Ctx.JEqH.toUnbounded {H : Set Jdg} {Γ : Ctx} {A a b : Tm 0}
    (h : Ctx.JEqH H Γ A a b) : Ctx.JEqB .unbounded H Γ A a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.toUnbounded h

/-- Unrestricted-budget derivability is exactly the original extensional W calculus. -/
theorem Ctx.JEqB.unbounded_iff {H : Set Jdg} {Γ : Ctx} {A a b : Tm 0} :
    Ctx.JEqB .unbounded H Γ A a b ↔ Ctx.JEqH H Γ A a b :=
  ⟨Ctx.JEqB.forget, Ctx.JEqH.toUnbounded⟩

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
