module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.NamedSubstitution
public import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.TypedSubstitution

@[expose] public section

/-!
# Same-bound free-name substitution of actual bounded derivations

Every mapped lookup has an actual target-theory typing derivation, and the target
context is well formed at the original bound. General hypothesis transport is
explicit: substitution acts on original theory leaves, and context transport
lifts variable-image proofs under binders. The original empty-theory APIs remain.
Cofinite binders exclude the replaced name, target declarations and replacement
free names.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W

theorem Ctx.SubstB.cons_of_hypotheses {levels : RuleBudget} {H : Set Jdg} {x : String} {v : Tm 0}
    (hw : HypothesisTransport levels H H) {Γ Δ : Ctx} {y : String} {A : Tm 0}
    (e : Ctx.SubstB levels x v Γ Δ H) (hy : y ≠ x) (hyΔ : y ∉ Δ.dv)
    (hctx : (Δ.cons y (A.fsubst x v)).JEqB levels H .unit .star .star) :
    Ctx.SubstB levels x v (Γ.cons y A) (Δ.cons y (A.fsubst x v)) H :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.lookup_subst_cons_of_hypotheses hw e hy hyΔ hctx

/-- Every inference rule retains the original cap and exact substituted source terms. -/
theorem Ctx.JEqB.substitute_of_hypotheses {levels : RuleBudget} {H H' : Set Jdg} {Γ : Ctx} {A a b : Tm 0}
    (hw : HypothesisTransport levels H' H') (x : String) (v : Tm 0)
    (hs : HypothesisSubstitution levels H H' x v) (d : Γ.JEqB levels H A a b) (Δ : Ctx)
    (e : Ctx.SubstB levels x v Γ Δ H') (hΔ : Δ.JEqB levels H' .unit .star .star) :
    Δ.JEqB levels H' (A.fsubst x v) (a.fsubst x v) (b.fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.substitution_of_hypotheses x v hw hs d Δ e hΔ

theorem Ctx.JEqB.substitute_last_of_hypotheses {levels : RuleBudget} {H H' : Set Jdg} {x : String} {v : Tm 0}
    (hw : HypothesisTransport levels H' H') (hs : HypothesisSubstitution levels H H' x v)
    {Γ : Ctx} {A B b b' : Tm 0} (hΓ : Γ.JEqB levels H' .unit .star .star)
    (hv : Γ.JEqB levels H' A v v) (hxΓ : x ∉ Γ.typeFvs) (hxA : x ∉ A.fvs)
    (d : (Γ.cons x A).JEqB levels H B b b') :
    Γ.JEqB levels H' (B.fsubst x v) (b.fsubst x v) (b'.fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.substitute_last_of_hypotheses hw hs hΓ hv hxΓ hxA d

theorem Ctx.JEqB.instantiate_of_hypotheses {levels : RuleBudget} {H H' : Set Jdg} {Γ : Ctx} {v A : Tm 0}
    {B b b' : Tm 1} {L : Finset String} (hw : HypothesisTransport levels H' H')
    (hs : ∀ x, HypothesisSubstitution levels H H' x v)
    (hΓ : Γ.JEqB levels H' .unit .star .star) (hv : Γ.JEqB levels H' A v v)
    (d : ∀ y ∉ L, (Γ.cons y A).JEqB levels H (B.open y) (b.open y) (b'.open y)) :
    Γ.JEqB levels H' (B.lst v) (b.lst v) (b'.lst v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_of_hypotheses hw hs hΓ hv d

theorem StructuralTheory.contextClosure {levels : RuleBudget} {H : Set Jdg} (h : ClosedHypotheses H) :
    StructuralTheory levels (ContextClosure H) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.contextClosure_structural levels h

theorem Ctx.SubstB.cons {levels : RuleBudget} {x : String} {v : Tm 0} {Γ Δ : Ctx}
    {y : String} {A : Tm 0} (e : Ctx.SubstB levels x v Γ Δ)
    (hy : y ≠ x) (hyΔ : y ∉ Δ.dv)
    (hctx : (Δ.cons y (A.fsubst x v)).JEqB levels ∅ .unit .star .star) :
    Ctx.SubstB levels x v (Γ.cons y A) (Δ.cons y (A.fsubst x v)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.lookup_subst_cons e hy hyΔ hctx

theorem Ctx.JEqB.substitute {levels : RuleBudget} {Γ : Ctx} {A a b : Tm 0}
    (h : Γ.JEqB levels ∅ A a b) (x : String) (v : Tm 0) (Δ : Ctx)
    (e : Ctx.SubstB levels x v Γ Δ) (hΔ : Δ.JEqB levels ∅ .unit .star .star) :
    Δ.JEqB levels ∅ (A.fsubst x v) (a.fsubst x v) (b.fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.substitution x v h Δ e hΔ

theorem Ctx.SubstB.drop {levels : RuleBudget} {H : Set Jdg} {x : String} {v : Tm 0} {Γ : Ctx} {A : Tm 0}
    (hΓ : Γ.JEqB levels H .unit .star .star) (hv : Γ.JEqB levels H A v v)
    (hxΓ : x ∉ Γ.typeFvs) (hxA : x ∉ A.fvs) :
    Ctx.SubstB levels x v (Γ.cons x A) Γ H :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.drop_lookup hΓ hv hxΓ hxA

theorem Ctx.JEqB.substitute_last {levels : RuleBudget} {x : String} {v : Tm 0} {Γ : Ctx}
    {A B b b' : Tm 0} (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hv : Γ.JEqB levels ∅ A v v) (hxΓ : x ∉ Γ.typeFvs) (hxA : x ∉ A.fvs)
    (h : (Γ.cons x A).JEqB levels ∅ B b b') :
    Γ.JEqB levels ∅ (B.fsubst x v) (b.fsubst x v) (b'.fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.substitute_last hΓ hv hxΓ hxA h

theorem Ctx.JEqB.instantiate {levels : RuleBudget} {Γ : Ctx} {v A : Tm 0} {B b b' : Tm 1}
    {L : Finset String} (hΓ : Γ.JEqB levels ∅ .unit .star .star)
    (hv : Γ.JEqB levels ∅ A v v)
    (h : ∀ y ∉ L, (Γ.cons y A).JEqB levels ∅ (B.open y) (b.open y) (b'.open y)) :
    Γ.JEqB levels ∅ (B.lst v) (b.lst v) (b'.lst v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate hΓ hv h

theorem instantiate_nat_successor : Ctx.JEqB 1 ∅ .nil .nats (.succ .zero) (.succ .zero) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.Inductives.W.instantiate_nat_successor

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.Inductives.W
