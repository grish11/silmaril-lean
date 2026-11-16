module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.TheoryStructure.Defs
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure

public section

/-!
# Structural weakening for extensional derivations

Lookup-preserving context embeddings transport every existing `ECtx.JEqH`
rule into an actually well-formed target context. Cofinite binder premises
exclude the target declarations and are lifted through matching binders.
Reflection, UIP, function/sum extensionality and every Nat beta rule are
included. Arbitrary theories provide a transport contract only for original
hypothesis leaves. The closed specialization has empty judgment hypotheses;
free-name contexts may be nonempty.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Every context embeds into itself by preserving each actual lookup. -/
theorem ECtx.Embeds.refl (Γ : ECtx) : Γ.Embeds Γ := fun h => h

/-- Lookup-preserving context embeddings compose. -/
theorem ECtx.Embeds.trans {Γ Δ Ξ : ECtx} (h : Γ.Embeds Δ) (h' : Δ.Embeds Ξ) :
    Γ.Embeds Ξ := fun hx => h' (h hx)

/-- An embedding lifts beneath the same free-name declaration. -/
theorem ECtx.Embeds.cons {Γ Δ : ECtx} (h : Γ.Embeds Δ) (x : String) (A : ETm 0) :
    (Γ.cons x A).Embeds (Δ.cons x A) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure.embedding_cons h x A

/-- Adding a fresh name preserves all previous lookups. -/
theorem ECtx.Embeds.fresh {Γ : ECtx} {x : String} (hx : x ∉ Γ.dv) (A : ETm 0) :
    Γ.Embeds (Γ.cons x A) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure.embedding_fresh hx A

/-- Every closed extensional equality has an actual well-formedness judgment for its context. -/
theorem ECtx.JEqH.context {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqH ∅ Γ A a b) :
    ECtx.JEqH ∅ Γ .unit .star .star :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure.context h

/-- All closed equality rules weaken into a lookup-preserving, actually well-formed context. -/
theorem ECtx.JEqH.weaken {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEqH ∅ Γ A a b)
    {Δ : ECtx} (hΔ : ECtx.JEqH ∅ Δ .unit .star .star) (hΓΔ : Γ.Embeds Δ) :
    ECtx.JEqH ∅ Δ A a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure.weaken h hΔ hΓΔ

/-- Every equality rule transports arbitrary theories using only original leaf transport. -/
theorem ECtx.JEqH.weaken_of_hypotheses {H K : Set EJdg} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqH H Γ A a b) (hh : HypothesisTransport H K)
    {Δ : ECtx} (hΔ : ECtx.JEqH K Δ .unit .star .star) (hΓΔ : Γ.Embeds Δ) :
    ECtx.JEqH K Δ A a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure.weaken_of_hypotheses
    h hh hΔ hΓΔ

/-- A fresh well-formed declaration can be added to any complete closed derivation. -/
theorem ECtx.JEqH.weaken_last {Γ : ECtx} {A a b B : ETm 0} {x : String} {n : ℕ}
    (h : ECtx.JEqH ∅ Γ A a b) (hx : x ∉ Γ.dv) (hB : ECtx.JEqH ∅ Γ (.univ n) B B) :
    ECtx.JEqH ∅ (Γ.cons x B) A a b :=
  h.weaken (.cons_ok h.context hx hB) (ECtx.Embeds.fresh hx B)

/-- The original hypothesis-free calculus inherits the same all-rule weakening theorem. -/
theorem ECtx.JEq.weaken {Γ : ECtx} {A a b : ETm 0} (h : ECtx.JEq Γ A a b)
    {Δ : ECtx} (hΔ : ECtx.JEq Δ .unit .star .star) (hΓΔ : Γ.Embeds Δ) : ECtx.JEq Δ A a b :=
  ECtx.JEqH.of_empty (ECtx.JEqH.weaken (h.toJEqH (H := ∅)) hΔ.toJEqH hΓΔ)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
