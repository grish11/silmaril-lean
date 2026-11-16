module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.NamedSubstitution
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.TypedNamedSubstitution

public section

/-!
# Free-name substitution for closed extensional derivations

Every source lookup is mapped to an actual typing in an actually well-formed
target context. Cofinite binders exclude the replaced name, target declarations
and replacement free names. All existing rules, including reflection, UIP and
function/sum extensionality, are preserved. Closed means empty judgment
hypotheses; the free-name contexts may be nonempty.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT

/-- Actual lookup images extend beneath a fresh matching declaration. -/
theorem ECtx.Subst.cons {x : String} {v : ETm 0} {Γ Δ : ECtx}
    {y : String} {A : ETm 0} (e : ECtx.Subst x v Γ Δ)
    (hy : y ≠ x) (hyΔ : y ∉ Δ.dv)
    (hctx : ECtx.JEqH ∅ (Δ.cons y (A.fsubst x v)) .unit .star .star) :
    ECtx.Subst x v (Γ.cons y A) (Δ.cons y (A.fsubst x v)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.TypedNamedSubstitution.lookup_subst_cons e hy hyΔ hctx

/-- Every existing closed equality rule preserves actual typed free-name substitution. -/
theorem ECtx.JEqH.substitute {Γ : ECtx} {A a b : ETm 0}
    (h : ECtx.JEqH ∅ Γ A a b) (x : String) (v : ETm 0) (Δ : ECtx)
    (e : ECtx.Subst x v Γ Δ) (hΔ : ECtx.JEqH ∅ Δ .unit .star .star) :
    ECtx.JEqH ∅ Δ (A.fsubst x v) (a.fsubst x v) (b.fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.TypedNamedSubstitution.substitution x v h Δ e hΔ

/-- A typed term supplies the newest lookup while every earlier lookup is preserved. -/
theorem ECtx.Subst.drop {x : String} {v : ETm 0} {Γ : ECtx} {A : ETm 0}
    (hΓ : ECtx.JEqH ∅ Γ .unit .star .star) (hv : ECtx.JEqH ∅ Γ A v v)
    (hxΓ : x ∉ Γ.typeFvs) (hxA : x ∉ A.fvs) :
    ECtx.Subst x v (Γ.cons x A) Γ :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.TypedNamedSubstitution.drop_lookup hΓ hv hxΓ hxA

/-- Substitute an actual typed term for the newest fresh free-name declaration. -/
theorem ECtx.JEqH.substitute_last {x : String} {v : ETm 0} {Γ : ECtx}
    {A B b b' : ETm 0} (hΓ : ECtx.JEqH ∅ Γ .unit .star .star)
    (hv : ECtx.JEqH ∅ Γ A v v) (hxΓ : x ∉ Γ.typeFvs) (hxA : x ∉ A.fvs)
    (h : ECtx.JEqH ∅ (Γ.cons x A) B b b') :
    ECtx.JEqH ∅ Γ (B.fsubst x v) (b.fsubst x v) (b'.fsubst x v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.TypedNamedSubstitution.substitute_last hΓ hv hxΓ hxA h

/-- Cofinite binder premises instantiate at any actually typed argument. -/
theorem ECtx.JEqH.instantiate {Γ : ECtx} {v A : ETm 0} {B b b' : ETm 1}
    {L : Finset String} (hΓ : ECtx.JEqH ∅ Γ .unit .star .star)
    (hv : ECtx.JEqH ∅ Γ A v v)
    (h : ∀ y ∉ L, ECtx.JEqH ∅ (Γ.cons y A) (B.open y) (b.open y) (b'.open y)) :
    ECtx.JEqH ∅ Γ (B.lst v) (b.lst v) (b'.lst v) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.TypedNamedSubstitution.instantiate hΓ hv h

end Silmaril.Logic.TypeTheory.ExtensionalMLTT
