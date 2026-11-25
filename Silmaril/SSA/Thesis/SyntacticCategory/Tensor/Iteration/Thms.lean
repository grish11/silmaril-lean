module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Distributivity.Thms
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Iteration

/-! # Uniform Elgot iteration in the distributive syntactic Freyd category -/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory CategoryTheory.Limits

variable {S : Sig.{u}}

/-- The chosen categorical coproduct form of iteration is uniform along pure arrows. -/
theorem iterate'_uniformity {A A' B : SynCat S} (f : A ⟶ B ⨿ A)
    (g : A' ⟶ B ⨿ A') (k : A ⟶ A') (hk : IsPureMor k)
    (square : f ≫ coprod.map (𝟙 B) k = k ≫ g) : iterate' f = k ≫ iterate' g :=
  iterate'_uniformity_proof f g k hk square

/-- The syntactic computation category uses the iteration induced by syntax. -/
noncomputable instance computationIteration (S : Sig.{u}) : Iteration (SynCat S) :=
  iterationStructure S

/-- The syntactic computation iteration satisfies the Elgot iteration equations. -/
instance computationElgot (S : Sig.{u}) : ElgotCategory (SynCat S) :=
  elgotCategory S

/-- The distributive Freyd inclusion supplies uniformity for its chosen iteration. -/
noncomputable instance valuesElgotFreyd (S : Sig.{u}) : ElgotFreydCategory (values S) where
  uniformity f g h comm := iterate'_uniformity f g h.hom h.property comm

end Silmaril.Thesis.LambdaIter.Syn.SynCat
