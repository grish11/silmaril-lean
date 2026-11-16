module

public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Motive.Defs
public import Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination.Thms
import Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive

public section

/-!
# Actual packaging of arbitrary two-binder identity motives

Closed derivational weakening forms the path domain beneath the endpoint
binder. Actual cofinite formation of an arbitrary `ETm 2` motive then gives
both abstractions of `packageMotive` their stated function type. The level
`max k (n+1)` accounts for the universe-valued codomain. No function-valued
motive typing is assumed as a certificate.

Actual typed free-name substitution instantiates the endpoint beneath the
path declaration. Two checked beta steps identify the packaged application
with direct double instantiation of `C`, so the derived eliminator is typed
at that direct motive instance.
-/

namespace Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination

/-- Opening the endpoint binder reveals its path-function fiber. -/
theorem motiveFiber_open (A a : ETm 0) (n : ℕ) (x : String) :
    (motiveFiber A a n).open x = .pi (.id A a (.fv x)) (.univ n) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive.motiveFiber_open A a n x

/-- Opening the endpoint of the packaged body leaves the path abstraction. -/
theorem packageBody_open (A a : ETm 0) (C : ETm 2) (x : String) :
    ((.abs (.id A.wk0 a.wk0 (.bv 0)) C : ETm 1).open x) =
      .abs (.id A a (.fv x)) (C.open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive.packageBody_open A a C x

/-- Instantiating the endpoint of the packaged body leaves the path abstraction. -/
theorem packageBody_lst (A a b : ETm 0) (C : ETm 2) :
    ((.abs (.id A.wk0 a.wk0 (.bv 0)) C : ETm 1).lst b) =
      .abs (.id A a b) (C.lst b) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive.packageBody_lst A a b C

/-- Actual weakening forms the endpoint-indexed identity domain in the extended context. -/
theorem endpointId_formation {Γ : ECtx} {A a : ETm 0} {k : ℕ}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a)
    {x : String} (hx : x ∉ Γ.dv) :
    ECtx.JEqH ∅ (Γ.cons x A) (.univ k) (.id A a (.fv x)) (.id A a (.fv x)) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive.endpointId_formation hA ha hx

/-- The complete path-function fiber has actual cofinite formation. -/
theorem motiveFiber_formation {Γ : ECtx} {A a : ETm 0} {k n : ℕ}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a) :
    ∀ x ∉ Γ.dv, ECtx.JEqH ∅ (Γ.cons x A) (.univ (max k (n + 1)))
      ((motiveFiber A a n).open x) ((motiveFiber A a n).open x) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive.motiveFiber_formation hA ha

/-- The function-valued motive type is formed from the actual carrier and base typing. -/
theorem motiveType_formation {Γ : ECtx} {A a : ETm 0} {k n : ℕ}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a) :
    ECtx.JEqH ∅ Γ (.univ (max k (n + 1))) (motiveType A a n) (motiveType A a n) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive.motiveType_formation hA ha

/-- Actual two-binder motive formation derives both abstractions of the packaged motive. -/
theorem packageMotive_typing {Γ : ECtx} {A a : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqH ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y)) :
    ECtx.JEqH ∅ Γ (motiveType A a n) (packageMotive A a C) (packageMotive A a C) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive.packageMotive_typing hA ha hC

/-- A genuinely packaged arbitrary motive can be supplied to the derived eliminator. -/
theorem packagedBasedJ_congr {Γ : ECtx} {A a b p d d' : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqH ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (hb : ECtx.JEqH ∅ Γ A b b) (hp : ECtx.JEqH ∅ Γ (.id A a b) p p)
    (hd : ECtx.JEqH ∅ Γ (value (packageMotive A a C) a (.refl a)) d d') :
    ECtx.JEqH ∅ Γ (value (packageMotive A a C) b p) (basedJ d b p) (basedJ d' b p) :=
  basedJ_congr hA.context (.cumul (Nat.le_max_left k (n + 1)) hA)
    (motiveFiber_formation hA ha) (packageMotive_typing hA ha hC) ha hb hp hd

/-- Two actual checked beta steps identify arbitrary packaged motives with direct instantiation. -/
theorem packageMotive_value {Γ : ECtx} {A a b p : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqH ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (hb : ECtx.JEqH ∅ Γ A b b) (hp : ECtx.JEqH ∅ Γ (.id A a b) p p) :
    ECtx.JEqH ∅ Γ (.univ n) (value (packageMotive A a C) b p) ((C.lst b).lst p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive.packageMotive_value hA ha hC hb hp

/-- Based identity elimination is typed at the arbitrary motive's direct double instance. -/
theorem directBasedJ_congr {Γ : ECtx} {A a b p d d' : ETm 0} {C : ETm 2} {k n : ℕ}
    {L : Finset String} {K : String → Finset String}
    (hA : ECtx.JEqH ∅ Γ (.univ k) A A) (ha : ECtx.JEqH ∅ Γ A a a)
    (hC : ∀ x ∉ L, ∀ y ∉ K x,
      ECtx.JEqH ∅ ((Γ.cons x A).cons y (.id A a (.fv x))) (.univ n)
        ((C.open x).open y) ((C.open x).open y))
    (hb : ECtx.JEqH ∅ Γ A b b) (hp : ECtx.JEqH ∅ Γ (.id A a b) p p)
    (hd : ECtx.JEqH ∅ Γ ((C.lst a).lst (.refl a)) d d') :
    ECtx.JEqH ∅ Γ ((C.lst b).lst p) (basedJ d b p) (basedJ d' b p) :=
  Silmaril.Proofs.Logic.TypeTheory.ExtensionalMLTT.IdentityMotive.directBasedJ_congr hA ha hC hb hp hd

end Silmaril.Logic.TypeTheory.ExtensionalMLTT.IdentityElimination
