module

public import Silmaril.Games.Abstract.SessionLinkAssoc.Defs

/-!
# Coherence of linking sessions (definitions)

`SessionLinkAssoc` proves that `SessionLink.linkS` is associative and unital up to transport of
the store along an equivalence (`SessionLinkAssoc.mapStore`). This topic adds the coherence of
these isomorphisms: `linkS` is natural in both stores, `mapStore` is functorial, and the two ways
of reassociating a fourfold link, and the two ways of removing a unit from a threefold link, give
the same store equivalence. The comparisons are equivalences built from `Equiv.prodAssoc` and the
unitors `Equiv.prodPUnit` and `Equiv.punitProd`; they are named here.

**Pentagon.** Reassociating `linkS (linkS (linkS t u) v) w` into `linkS t (linkS u (linkS v w))`
in two steps (`assoc4Two`) or in three steps (`assoc4Three`). Both are equivalences
`S₁ × (S₂ × (S₃ × S₄)) ≃ ((S₁ × S₂) × S₃) × S₄`, in the direction of `mapStore` in
`SessionLinkAssoc.linkS_assoc`.

**Triangle.** Removing the identity session from `linkS (linkS t idS) u`, through the right unit
(`unitRight`) or through associativity and the left unit (`unitAssocLeft`). Both are
equivalences `S × S' ≃ (S × PUnit) × S'`.

Theorems in `Silmaril.Games.Abstract.SessionLinkCoh.Thms`.
-/

@[expose] public section

namespace Silmaril.Games.Abstract.SessionLinkCoh

universe u

variable (S₁ S₂ S₃ S₄ S S' : Type u)

/-- Reassociation in two steps: `linkS_assoc` on `(linkS t u, v, w)`, then on `(t, u, linkS v w)`. -/
def assoc4Two : S₁ × (S₂ × (S₃ × S₄)) ≃ ((S₁ × S₂) × S₃) × S₄ :=
  (Equiv.prodAssoc S₁ S₂ (S₃ × S₄)).symm.trans (Equiv.prodAssoc (S₁ × S₂) S₃ S₄).symm

/-- Reassociation in three steps: `linkS_assoc` on `(t, u, v)` inside, on `(t, linkS u v, w)`, and
on `(u, v, w)` inside. -/
def assoc4Three : S₁ × (S₂ × (S₃ × S₄)) ≃ ((S₁ × S₂) × S₃) × S₄ :=
  (Equiv.prodCongr (Equiv.refl S₁) (Equiv.prodAssoc S₂ S₃ S₄).symm).trans
    ((Equiv.prodAssoc S₁ (S₂ × S₃) S₄).symm.trans
      (Equiv.prodCongr (Equiv.prodAssoc S₁ S₂ S₃).symm (Equiv.refl S₄)))

/-- Removing the unit from `linkS (linkS t idS) u` by the right unit law. -/
def unitRight : S × S' ≃ (S × PUnit.{u + 1}) × S' :=
  Equiv.prodCongr (Equiv.prodPUnit S).symm (Equiv.refl S')

/-- Removing the unit from `linkS (linkS t idS) u` by associativity and the left unit law. -/
def unitAssocLeft : S × S' ≃ (S × PUnit.{u + 1}) × S' :=
  (Equiv.prodCongr (Equiv.refl S) (Equiv.punitProd S').symm).trans
    (Equiv.prodAssoc S PUnit.{u + 1} S').symm

end Silmaril.Games.Abstract.SessionLinkCoh
