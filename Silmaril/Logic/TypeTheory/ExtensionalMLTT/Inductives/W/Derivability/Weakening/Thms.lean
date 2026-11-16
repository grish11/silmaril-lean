module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.Derivability.Weakening.Defs
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.TypedWeakening

@[expose] public section

/-!
# Weakening of bounded object derivations

These theorems act on derivations. Arbitrary contextual judgment hypotheses
use an explicit transport contract; `ContextClosure` constructs one by enlarging
the theory. The original empty-theory API is retained. Terms and universe bounds
are unchanged.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem Ctx.LookupLE.refl (Γ : Ctx) : Γ.LookupLE Γ := fun h => h

theorem Ctx.LookupLE.trans {Γ Δ Ξ : Ctx} (h : Γ.LookupLE Δ) (k : Δ.LookupLE Ξ) :
    Γ.LookupLE Ξ := fun e => k (h e)

theorem Ctx.LookupLE.cons {Γ Δ : Ctx} (e : Γ.LookupLE Δ) (x : String) (A : Tm 0) :
    (Γ.cons x A).LookupLE (Δ.cons x A) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.lookupLE_cons e x A

theorem Ctx.LookupLE.fresh_cons {Γ : Ctx} {x : String} (hx : x ∉ Γ.dv) (A : Tm 0) :
    Γ.LookupLE (Γ.cons x A) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.lookupLE_fresh hx A

theorem ContextClosure.includes (H : Set Jdg) : H ⊆ ContextClosure H :=
  fun j hj => ⟨j.Γ, hj, Ctx.LookupLE.refl _⟩

theorem ContextClosure.mono {H K : Set Jdg} (h : H ⊆ K) : ContextClosure H ⊆ ContextClosure K := by
  intro j hj
  obtain ⟨Γ, hΓ, e⟩ := hj
  exact ⟨Γ, h hΓ, e⟩

theorem ContextClosure.empty : ContextClosure ∅ = ∅ := by
  apply Set.Subset.antisymm
  · intro j hj
    obtain ⟨Γ, hΓ, _⟩ := hj
    exact False.elim hΓ
  · intro j hj
    exact False.elim hj

/-- Closing a theory twice adds no new contextual hypotheses. -/
theorem ContextClosure.idempotent (H : Set Jdg) : ContextClosure (ContextClosure H) = ContextClosure H := by
  apply Set.Subset.antisymm
  · intro j hj
    obtain ⟨Δ, ⟨Γ, hΓ, e⟩, f⟩ := hj
    exact ⟨Γ, hΓ, e.trans f⟩
  · exact ContextClosure.includes _

/-- Original hypothesis membership produces an actual derivation in the enlarged context. -/
theorem ContextClosure.transport (levels : RuleBudget) (H : Set Jdg) :
    HypothesisTransport levels H (ContextClosure H) :=
  fun hj e _ => .hyp ⟨_, hj, e⟩

theorem ContextClosure.self_transport (levels : RuleBudget) (H : Set Jdg) :
    HypothesisTransport levels (ContextClosure H) (ContextClosure H) := by
  intro Γ Δ A a b hj e _
  obtain ⟨Ξ, hΞ, f⟩ := hj
  exact .hyp ⟨Ξ, hΞ, f.trans e⟩

theorem HypothesisTransport.empty (levels : RuleBudget) (H : Set Jdg) : HypothesisTransport levels ∅ H :=
  fun hj _ _ => False.elim hj

/-- Transport is required only for the original theory leaves. -/
theorem Ctx.JEqB.weaken_of_hypotheses {levels : RuleBudget} {H H' : Set Jdg} {Γ Δ : Ctx} {A a b : Tm 0}
    (hh : HypothesisTransport levels H H') (d : Γ.JEqB levels H A a b) (e : Γ.LookupLE Δ)
    (hΔ : Δ.JEqB levels H' .unit .star .star) : Δ.JEqB levels H' A a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.weakening_of_hypotheses hh d Δ e hΔ

theorem Ctx.JEqB.weaken_contextClosure {levels : RuleBudget} {H : Set Jdg} {Γ Δ : Ctx} {A a b : Tm 0}
    (d : Γ.JEqB levels H A a b) (e : Γ.LookupLE Δ)
    (hΔ : Δ.JEqB levels (ContextClosure H) .unit .star .star) :
    Δ.JEqB levels (ContextClosure H) A a b :=
  Ctx.JEqB.weaken_of_hypotheses (ContextClosure.transport levels H) d e hΔ

/-- Fresh extension uses only actual transport of the original theory leaves. -/
theorem Ctx.JEqB.weaken_cons_of_hypotheses {levels : RuleBudget} {n : ℕ} {H : Set Jdg} {Γ : Ctx}
    {x : String} {B : Tm 0} (hh : HypothesisTransport levels H H)
    (h : Γ.JEqB levels H .unit .star .star) (hx : x ∉ Γ.dv) (hn : RuleBudget.Allows levels n)
    (hB : Γ.JEqB levels H (.univ n) B B) {A a b : Tm 0}
    (d : Γ.JEqB levels H A a b) : (Γ.cons x B).JEqB levels H A a b :=
  Ctx.JEqB.weaken_of_hypotheses hh d (Ctx.LookupLE.fresh_cons hx B) (.cons_ok hn h hx hB)

/-- All 38 inference rules preserve the original bound under well-formed weakening. -/
theorem Ctx.JEqB.weaken {levels : RuleBudget} {Γ Δ : Ctx} {A a b : Tm 0}
    (h : Γ.JEqB levels ∅ A a b) (e : Γ.LookupLE Δ)
    (hΔ : Δ.JEqB levels ∅ .unit .star .star) : Δ.JEqB levels ∅ A a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.weakening h Δ e hΔ

/-- Add one fresh declaration, preserving every term and inference-rule universe. -/
theorem Ctx.JEqB.weaken_cons {levels : RuleBudget} {n : ℕ} {Γ : Ctx} {x : String} {B : Tm 0}
    (h : Γ.JEqB levels ∅ .unit .star .star) (hx : x ∉ Γ.dv) (hn : RuleBudget.Allows levels n)
    (hB : Γ.JEqB levels ∅ (.univ n) B B) {A a b : Tm 0}
    (d : Γ.JEqB levels ∅ A a b) : (Γ.cons x B).JEqB levels ∅ A a b :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.weakening_cons h hx hn hB d

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
