module

public import Silmaril.Semantics.Calco2019.Defs

/-! # Nested guarded summands in Notation 7 -/

@[expose] public section

universe u v

namespace Silmaril.Calco2019

open CategoryTheory

variable {K : Type u} [Category.{v} K] (P : Coproducts K)

namespace Coproducts

/-- The inverse direction of the selected coproduct reassociation. -/
theorem assocInv_assoc (X Y Z : K) :
    P.assocInv (X := X) (Y := Y) (Z := Z) ≫ P.assoc = 𝟙 _ := by
  apply P.hom_ext
  · simp [assoc, assocInv, map]
  · apply P.hom_ext <;> simp [assoc, assocInv, map]

/-- Reassociate the left-nested list of summands, keeping the first summand
separate. The list consists of the intervening summands before the final one. -/
def reassociate : (first last : K) → (middle : List K) →
    P.sum (middle.foldl P.sum first) last ≅ P.sum first (middle.foldr P.sum last)
  | _, _, [] => Iso.refl _
  | first, last, next :: middle =>
    reassociate (P.sum first next) last middle ≪≫
      { hom := P.assoc
        inv := P.assocInv
        hom_inv_id := P.assoc_assocInv _ _ _
        inv_hom_id := P.assocInv_assoc _ _ _ }
termination_by structural _ _ middle => middle

end Coproducts

namespace Guardedness

variable {P} (G : Guardedness P)

/-- Notation 7 with any positive number of right summands. -/
def nestedMany {X Y : K} (middle : List K) (last : K)
    (f : X ⟶ P.sum (middle.foldl P.sum Y) last) : Prop :=
  G.guarded (f ≫ (P.reassociate Y last middle).hom)

theorem nestedMany_nil {X Y Z : K} (f : X ⟶ P.sum Y Z) :
    G.nestedMany [] Z f ↔ G.guarded f := by
  simp [nestedMany, Coproducts.reassociate]

theorem nestedMany_singleton {X Y Z W : K} (f : X ⟶ P.sum (P.sum Y Z) W) :
    G.nestedMany [Z] W f ↔ G.nested f := by
  simp [nestedMany, nested, Coproducts.reassociate]

end Guardedness
end Silmaril.Calco2019
