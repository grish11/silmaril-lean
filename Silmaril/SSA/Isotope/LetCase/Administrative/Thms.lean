module

public import Silmaril.SSA.Isotope.LetCase.Administrative.Defs
public import Silmaril.Raw.SSA.Isotope.LetCase.LocallyNameless.Equiv
import Silmaril.Proofs.SSA.Isotope.LetCase.Administrative

/-! # Administrative moves keep the native meaning

A value is pure, so a let of a value is natively equal to its body with
the value substituted, by pure let beta. A pattern let of a pair of values
is natively equal to its body with both values substituted, by pair beta
and two pure let betas. So a pass of administrative moves, and any number
of passes, gives a natively equal term.

Pair beta needs the types of the two components of the pair. They are
read from the type of the pair, so products of types must be injective.
The type formers of the abstract signature do not state that; the
concrete types `Ty` have it.

No request is moved, removed or duplicated: only values are substituted.
-/

public section

namespace Silmaril.Isotope.LetCase.LocallyNameless

universe u v w x

variable {ν : Type w} [DecidableEq ν] {τ : Type u} [TypeFormers τ] {Φ : Type v} [HasTy Φ τ]
  {ε : Type x} [HasEff Φ ε]

omit [DecidableEq ν] [TypeFormers τ] [HasTy Φ τ] in
/-- A value is pure. -/
theorem Tm.pure_of_isValue (pe : ε) {n : Nat} (t : Tm ν Φ n) (h : t.isValue = true) : Pure pe t :=
  pure_of_isValue_proof pe t h

/-- One pass of administrative moves gives a natively equal term, when
products of types are injective. -/
theorem Equiv.administrative (pe : ε)
    (products : ∀ {A B C D : τ}, product A B = product C D → A = C ∧ B = D)
    {Γ : Isotope.Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) : Equiv pe Γ β t t.administrative A :=
  administrative_equiv_proof pe products h

/-- Any number of passes of administrative moves gives a natively equal
term, when products of types are injective. -/
theorem Equiv.administrative_iterate (pe : ε)
    (products : ∀ {A B C D : τ}, product A B = product C D → A = C ∧ B = D)
    {Γ : Isotope.Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {A : τ} (passes : Nat) {t : Tm ν Φ n}
    (h : HasType Φ Γ β t A) : Equiv pe Γ β t (Tm.administrative^[passes] t) A :=
  administrative_iterate_proof pe products passes h

/-- Products of the concrete types are injective. -/
theorem products_ty {α : Type u} {A B C D : Ty α} (h : product A B = product C D) :
    A = C ∧ B = D := by
  cases h
  exact ⟨rfl, rfl⟩

end Silmaril.Isotope.LetCase.LocallyNameless
