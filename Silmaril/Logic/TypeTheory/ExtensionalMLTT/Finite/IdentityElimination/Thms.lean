module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.Finite.Assignments.Thms
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Motive.Thms
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedIdentityElimination

public section

/-!
# Bounded identity elimination for arbitrary two-binder motives

Actual bounded carrier, endpoint and motive formation derives both packaged
abstractions, two beta steps to direct instantiation, and based path induction
using reflection, UIP and conversion. Every derivation shares `levels`, with
the explicit closure condition `max k (n + 1) < levels`. Motive instantiation
uses bounded typed assignments; no unbounded regularity or substitution is
used to produce a bounded result.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Bounded

/-- Actual same-budget weakening forms the endpoint-indexed identity domain. -/
theorem endpointId_formation {levels : ℕ} {Γ : ECtx} {A a : ETm 0} {k : ℕ} (hk : k < levels)
    (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A) (ha : ECtx.JEqB levels ∅ Γ A a a)
    {x : String} (hx : x ∉ Γ.dv) :
    ECtx.JEqB levels ∅ (Γ.cons x A) (.univ k) (.id A a (.fv x)) (.id A a (.fv x)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedIdentityElimination.endpointId_formation hk hA ha hx

/-- Arbitrary actual two-binder formation derives the packaged motive at the same budget. -/
theorem packageMotive_typing {levels : ℕ} {Γ : ECtx} {A a : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hlevels : max k (n + 1) < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A)
    (ha : ECtx.JEqB levels ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqB levels ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y)) :
    ECtx.JEqB levels ∅ Γ (motiveType A a n) (packageMotive A a C) (packageMotive A a C) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedIdentityElimination.packageMotive_typing hlevels hA ha hC

/-- Two actual bounded beta steps identify packaged values with direct double instantiation. -/
theorem packageMotive_value {levels : ℕ} {Γ : ECtx} {A a b p : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hlevels : max k (n + 1) < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A)
    (ha : ECtx.JEqB levels ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqB levels ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (hb : ECtx.JEqB levels ∅ Γ A b b) (hp : ECtx.JEqB levels ∅ Γ (.id A a b) p p) :
    ECtx.JEqB levels ∅ Γ (.univ n) (value (packageMotive A a C) b p) ((C.lst b).lst p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedIdentityElimination.packageMotive_value hlevels hA ha hC hb hp

/-- Actual bounded based identity elimination has the motive's direct endpoint/path instance. -/
theorem directBasedJ_congr {levels : ℕ} {Γ : ECtx} {A a b p d d' : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hlevels : max k (n + 1) < levels) (hA : ECtx.JEqB levels ∅ Γ (.univ k) A A)
    (ha : ECtx.JEqB levels ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqB levels ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (hb : ECtx.JEqB levels ∅ Γ A b b) (hp : ECtx.JEqB levels ∅ Γ (.id A a b) p p)
    (hd : ECtx.JEqB levels ∅ Γ ((C.lst a).lst (.refl a)) d d') :
    ECtx.JEqB levels ∅ Γ ((C.lst b).lst p) (basedJ d b p) (basedJ d' b p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.BoundedIdentityElimination.directBasedJ_congr hlevels hA ha hC hb hp hd

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Bounded
