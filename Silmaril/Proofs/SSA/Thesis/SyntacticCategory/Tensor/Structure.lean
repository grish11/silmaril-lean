module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Structure.Defs
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Defs

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory
open PremonoidalCategory

theorem valuesUnitIso_central_proof (S : Sig.{u}) :
    @IsCentral _ _ (computationTensor S) _ _ (valuesUnitIso S).hom := by
  constructor
  · intro X Y f
    change tensorRight X (𝟙 (tensorUnit S)) ≫ tensorLeft (tensorUnit S) f =
      tensorLeft (tensorUnit S) f ≫ tensorRight Y (𝟙 (tensorUnit S))
    simp
  · intro X Y f
    change tensorRight (tensorUnit S) f ≫ tensorLeft Y (𝟙 (tensorUnit S)) =
      tensorLeft X (𝟙 (tensorUnit S)) ≫ tensorRight (tensorUnit S) f
    simp

end Silmaril.Thesis.LambdaIter.Syn.SynCat
