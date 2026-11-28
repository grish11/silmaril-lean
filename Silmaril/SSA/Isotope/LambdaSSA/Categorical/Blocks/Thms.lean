module

public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Blocks.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.BlockIteration

/-! # Block elimination with feedback in both blocks -/

public section

universe v u

namespace Silmaril.Isotope.LambdaSSA.Semantics.Categorical

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasBinaryCoproducts C] (S : BlockSystem C) {Y : C}

/-- Solve the right block first, treating the left block as an exit. The
left entry of the joined loop is the loop of the left row with the right
block eliminated. The right entry is the right block's loop followed by
that left entry. Both rows may repeat into either block. -/
theorem BlockSystem.bekic (r : S.left ⟶ (Y ⨿ S.left) ⨿ S.right)
    (c : S.right ⟶ (Y ⨿ S.left) ⨿ S.right) :
    S.inl ≫ S.iter (S.joined r c) = S.iter (r ≫ coprod.desc (𝟙 _) (S.iter c)) ∧
    S.inr ≫ S.iter (S.joined r c) =
      S.iter c ≫ coprod.desc (𝟙 Y) (S.inl ≫ S.iter (S.joined r c)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Categorical.BlockIteration.bekic S r c

end Silmaril.Isotope.LambdaSSA.Semantics.Categorical
