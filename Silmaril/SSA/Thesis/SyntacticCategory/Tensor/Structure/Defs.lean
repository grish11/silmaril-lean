module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Thms

/-! # Tensor data for the syntactic computation category -/

@[expose] public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open scoped MonoidalCategory

variable {S : Sig.{u}}

/-- The tensor data uses the syntactic computations for whiskering and the
pure Cartesian structural maps. -/
@[instance_reducible] def computationTensor (S : Sig.{u}) : MonoidalCategoryStruct (SynCat S) where
  tensorObj := productObj
  whiskerLeft := tensorLeft
  whiskerRight f R := tensorRight R f
  tensorUnit := tensorUnit S
  associator A B C := (values S).mapIso
    (MonoidalCategoryStruct.associator (⟨A⟩ : ValueCat S) ⟨B⟩ ⟨C⟩)
  leftUnitor := tensorLeftUnitor
  rightUnitor := tensorRightUnitor

/-- The syntactic value and computation categories choose the same unit type. -/
def valuesUnitIso (S : Sig.{u}) :
    tensorUnit S ≅ (values S).obj (𝟙_ (ValueCat S)) :=
  Iso.refl _

end Silmaril.Thesis.LambdaIter.Syn.SynCat
