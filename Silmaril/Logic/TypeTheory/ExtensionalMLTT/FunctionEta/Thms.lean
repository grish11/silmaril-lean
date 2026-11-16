module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FunctionEta

@[expose] public section

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

namespace FunctionEta

/-- Opening an added outer binder leaves a term with no bound variables unchanged. -/
theorem closed_open (t : ETm 0) (x : String) : t.wk0.open x = t :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FunctionEta.closed_open t x

/-- Opening the eta body substitutes its actual fresh free variable. -/
theorem body_open (f : ETm 0) (x : String) :
    (ETm.app f.wk0 (.bv 0)).open x = .app f (.fv x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FunctionEta.body_open f x

/-- Instantiating a binder with a free variable agrees with opening it. -/
theorem lst_fv {k : ℕ} (t : ETm (k + 1)) (x : String) : t.lst (.fv x) = t.open x :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FunctionEta.lst_fv t x

end FunctionEta

/-- Eta expansion retains an actually formed dependent product and its actual typing. -/
theorem ECtx.JEqH.eta_expansion {Γ : ECtx} {n : ℕ} {A f : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ n) A A)
    (hB : ∀ x ∉ L, ECtx.JEqH ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : ECtx.JEqH ∅ Γ (.pi A B) f f) :
    ECtx.JEqH ∅ Γ (.pi A B) (.abs A (.app f.wk0 (.bv 0))) (.abs A (.app f.wk0 (.bv 0))) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FunctionEta.expansion hA hB hf

/-- Typed function eta follows from the existing beta and function-extensionality rules.
The codomain may depend on the bound argument; no global conversion hypothesis is used.
-/
theorem ECtx.JEqH.function_eta {Γ : ECtx} {n : ℕ} {A f : ETm 0} {B : ETm 1} {L : Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ n) A A)
    (hB : ∀ x ∉ L, ECtx.JEqH ∅ (Γ.cons x A) (.univ n) (B.open x) (B.open x))
    (hf : ECtx.JEqH ∅ Γ (.pi A B) f f) :
    ECtx.JEqH ∅ Γ (.pi A B) (.abs A (.app f.wk0 (.bv 0))) f :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.FunctionEta.equality hA hB hf

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
