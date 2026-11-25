module

public import Silmaril.SSA.Thesis.SyntacticCategory.Tensor.Structure.Defs
public import Silmaril.Semantics.Categories.Freyd.CentralUnit.Thms
import Silmaril.Proofs.SSA.Thesis.SyntacticCategory.Tensor.Structure

/-! # The shared unit in the syntactic computation tensor -/

public section

universe u

namespace Silmaril.Thesis.LambdaIter.Syn.SynCat

open CategoryTheory

/-- The chosen syntactic comparison commutes with both tensor actions on all
computation arrows. The proof uses the identity laws of the two endofunctors. -/
theorem valuesUnitIso_central (S : Sig.{u}) :
    @PremonoidalCategory.IsCentral _ _ (computationTensor S) _ _ (valuesUnitIso S).hom :=
  valuesUnitIso_central_proof S

end Silmaril.Thesis.LambdaIter.Syn.SynCat
