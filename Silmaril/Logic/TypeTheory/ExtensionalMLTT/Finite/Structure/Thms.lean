module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Derivation.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.DerivationStructure
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedStructure

public section

/-!
# Same-budget structural transport for all bounded extensional rules

Every closed `JEqB levels ∅` proof yields actual context well-formedness at
that same budget. Lookup-preserving context embeddings then transport all
34 rules into an actually well-formed target at `levels`. Cofinite premise
families exclude the target declarations and retain one common budget.

Closed means no judgment hypotheses; free-name contexts can be nonempty.
Arbitrary exact-context hypothesis theories are not assumed stable under
weakening.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- The original context is actually well formed at the same rule budget. -/
theorem ECtx.JEqB.context {levels : ℕ} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels ∅ Γ A a b) : ECtx.JEqB levels ∅ Γ .unit .star .star :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedStructure.context h

/-- All bounded rules transport along actual lookup embeddings without adding levels. -/
theorem ECtx.JEqB.weaken {levels : ℕ} {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqB levels ∅ Γ A a b) {Δ : ECtx}
    (hΔ : ECtx.JEqB levels ∅ Δ .unit .star .star) (e : Γ.Embeds Δ) :
    ECtx.JEqB levels ∅ Δ A a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedStructure.weaken h hΔ e

/-- Add a fresh actual declaration whose formation uses the same available levels. -/
theorem ECtx.JEqB.weaken_last {levels n : ℕ} {Γ : ECtx} {A a b B : ETm 0} {x : String}
    (h : ECtx.JEqB levels ∅ Γ A a b) (hn : n < levels) (hx : x ∉ Γ.dv)
    (hB : ECtx.JEqB levels ∅ Γ (.univ n) B B) :
    ECtx.JEqB levels ∅ (Γ.cons x B) A a b :=
  h.weaken (.cons_ok hn h.context hx hB) (ECtx.Embeds.fresh hx B)

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
