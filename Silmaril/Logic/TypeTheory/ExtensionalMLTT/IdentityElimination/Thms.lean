module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Defs
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination

public section

/-!
# Derived extensional based identity elimination

For an actual universe-valued function motive, equality reflection and UIP
identify the motive values at the base and at an arbitrary endpoint/path.
Conversion therefore transports the supplied base equality. Every application
has explicit domain and cofinite codomain formation premises. These are
derivations in the existing calculus, with no new inference rule.

The separate `IdentityElimination.Motive` module packages arbitrary two-binder
syntax from actual formation premises. Its applications are identified with direct
instantiation there using actual typed substitution and checked beta steps.
Preserving every intensional checked rule in extensional syntax remains a
separate translation proof.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination

/-- Instantiating an unused added outermost variable leaves the original term. -/
theorem lst_wkn_outermost {k : ℕ} (t : ETm k) (a : ETm 0) : (t.wkn k).lst a = t :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.lst_wkn_outermost t a

/-- The endpoint instantiation of the path-function fiber has the expected domain. -/
theorem motiveFiber_lst (A a b : ETm 0) (n : ℕ) :
    (motiveFiber A a n).lst b = .pi (.id A a b) (.univ n) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.motiveFiber_lst A a b n

/-- Reflection, UIP and dependent application identify the two motive values. -/
theorem value_congr {H : Set EJdg} {Γ : ECtx} {A a b p M : ETm 0} {n k : ℕ}
    {L : Finset String} (hΓ : ECtx.JEqH H Γ .unit .star .star)
    (hA : ECtx.JEqH H Γ (.univ k) A A)
    (hFiber : ∀ x ∉ L, ECtx.JEqH H (Γ.cons x A) (.univ k)
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x))
    (hM : ECtx.JEqH H Γ (motiveType A a n) M M)
    (ha : ECtx.JEqH H Γ A a a) (hb : ECtx.JEqH H Γ A b b)
    (hp : ECtx.JEqH H Γ (.id A a b) p p) :
    ECtx.JEqH H Γ (.univ n) (value M a (.refl a)) (value M b p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.value_congr
    hΓ hA hFiber hM ha hb hp

/-- The base equality gives dependent elimination at the supplied endpoint and path. -/
theorem basedJ_congr {H : Set EJdg} {Γ : ECtx} {A a b p M d d' : ETm 0} {n k : ℕ}
    {L : Finset String} (hΓ : ECtx.JEqH H Γ .unit .star .star)
    (hA : ECtx.JEqH H Γ (.univ k) A A)
    (hFiber : ∀ x ∉ L, ECtx.JEqH H (Γ.cons x A) (.univ k)
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x))
    (hM : ECtx.JEqH H Γ (motiveType A a n) M M)
    (ha : ECtx.JEqH H Γ A a a) (hb : ECtx.JEqH H Γ A b b)
    (hp : ECtx.JEqH H Γ (.id A a b) p p)
    (hd : ECtx.JEqH H Γ (value M a (.refl a)) d d') :
    ECtx.JEqH H Γ (value M b p) (basedJ d b p) (basedJ d' b p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.basedJ_congr
    hΓ hA hFiber hM ha hb hp hd

/-- At reflexivity the derived eliminator computes to the actually typed base. -/
theorem basedJ_beta {H : Set EJdg} {Γ : ECtx} {M a d : ETm 0}
    (hd : ECtx.JEqH H Γ (value M a (.refl a)) d d) :
    ECtx.JEqH H Γ (value M a (.refl a)) (basedJ d a (.refl a)) d :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.basedJ_beta hd

/-- The concrete unit motive has checked formation at every fresh endpoint. -/
theorem unitFiber_formed {H : Set EJdg} {Γ : ECtx}
    (hΓ : ECtx.JEqH H Γ .unit .star .star) :
    ∀ x ∉ Γ.dv, ECtx.JEqH H (Γ.cons x .unit) (.univ 1)
      ((motiveFiber .unit .star 0).open x) ((motiveFiber .unit .star 0).open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.unitFiber_formed hΓ

/-- Both abstractions of the concrete motive are derived in the existing calculus. -/
theorem unitMotive_typing {H : Set EJdg} {Γ : ECtx}
    (hΓ : ECtx.JEqH H Γ .unit .star .star) :
    ECtx.JEqH H Γ (motiveType .unit .star 0) unitMotive unitMotive :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.unitMotive_typing hΓ

/-- Two checked beta steps evaluate the concrete motive at its base point. -/
theorem unitMotive_value {H : Set EJdg} {Γ : ECtx}
    (hΓ : ECtx.JEqH H Γ .unit .star .star) :
    ECtx.JEqH H Γ (.univ 0) (value unitMotive .star (.refl .star)) .unit :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.unitMotive_value hΓ

/-- Conversion supplies an actual base inhabitant for the concrete motive. -/
theorem unitMotive_base {H : Set EJdg} {Γ : ECtx}
    (hΓ : ECtx.JEqH H Γ .unit .star .star) :
    ECtx.JEqH H Γ (value unitMotive .star (.refl .star)) .star .star :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.unitMotive_base hΓ

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination
