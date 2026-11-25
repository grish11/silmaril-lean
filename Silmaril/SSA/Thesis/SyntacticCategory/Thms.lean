module

public import Silmaril.Raw.SSA.Thesis.LambdaIter.Models.SynElgot
public import Silmaril.Raw.SSA.Thesis.LambdaIter.Models.SynUniformity
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Initial

/-! # The one-variable λiter syntactic category

Objects are the types of the signature. Arrows are one-variable typed terms
quotiented by the equational theory. The category has finite coproducts and
an iteration operation with fixpoint, naturality, codiagonal and uniformity
for arrows with a pure representative.

The empty type is initial. The proof of uniformity uses the syntactic
pure-arrow predicate.
-/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open LocallyNameless CategoryTheory CategoryTheory.Limits

variable {S : Sig.{u}}

/-- Any two arrows out of the empty type are identified by the empty-type equation. -/
theorem fromEmpty_unique (A : SynCat S)
    (f g : of (S := S) (empty : S.Ty) ⟶ A) : f = g :=
  fromEmpty_unique_proof A f g

/-- The empty-type elimination term exhibits the initial object. -/
def isInitialEmpty (S : Sig.{u}) : IsInitial (of (S := S) (empty : S.Ty)) :=
  IsInitial.ofUniqueHom
    (fun A => mk (HasType.abort (C := A.ty) HasType.newest))
    (fun A f => fromEmpty_unique A f _)

instance hasInitial (S : Sig.{u}) : HasInitial (SynCat S) :=
  (isInitialEmpty S).hasInitial

instance hasFiniteCoproducts (S : Sig.{u}) : HasFiniteCoproducts (SynCat S) :=
  hasFiniteCoproducts_of_has_binary_and_initial

/-- Iteration on the syntactic category satisfies the Elgot category laws. -/
theorem elgotCategory (S : Sig.{u}) :
    @ElgotCategory (SynCat S) _ _ (iterationStructure S) :=
  elgotCategory_of_hasFiniteCoproducts S

end Silmaril.Thesis.LambdaIter.Syn.SynCat
