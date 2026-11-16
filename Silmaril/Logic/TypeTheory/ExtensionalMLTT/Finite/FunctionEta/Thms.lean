module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Structure.Thms
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedFunctionEta

public section
namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Eta expansion retains the original finite rule budget and dependent product. -/
theorem ECtx.JEqB.eta_expansion {levels n : ℕ} {Γ : ECtx}
    {A f : ETm 0} {B : ETm 1} {L : Finset String} (hn : n < levels)
    (hA : ECtx.JEqB levels ∅ Γ (.univ n) A A)
    (hB : ∀ x ∉ L, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : ECtx.JEqB levels ∅ Γ (.pi A B) f f) :
    ECtx.JEqB levels ∅ Γ (.pi A B)
      (.abs A (.app f.wk0 (.bv 0))) (.abs A (.app f.wk0 (.bv 0))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedFunctionEta.expansion hn hA hB hf

/-- Function eta is derived from bounded beta and extensionality at the same
available levels. The codomain may depend on the argument. -/
theorem ECtx.JEqB.function_eta {levels n : ℕ} {Γ : ECtx}
    {A f : ETm 0} {B : ETm 1} {L : Finset String} (hn : n < levels)
    (hA : ECtx.JEqB levels ∅ Γ (.univ n) A A)
    (hB : ∀ x ∉ L, ECtx.JEqB levels ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : ECtx.JEqB levels ∅ Γ (.pi A B) f f) :
    ECtx.JEqB levels ∅ Γ (.pi A B) (.abs A (.app f.wk0 (.bv 0))) f :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedFunctionEta.equality hn hA hB hf

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
