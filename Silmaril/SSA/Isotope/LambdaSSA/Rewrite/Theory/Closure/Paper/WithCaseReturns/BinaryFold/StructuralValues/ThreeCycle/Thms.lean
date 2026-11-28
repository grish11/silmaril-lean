module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.Extension.Singleton.Iteration.Chosen.Blocks.ThreeCycle.Factorization.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Semantics.ITree.Typed.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldThreeCycle

/-! # The three-copy BinaryFold square cannot be factored through a partial fold -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold

open CategoryTheory CategoryTheory.Limits
open Semantics.Interaction.Typed (AtomValues)
open Paper.Extension.Singleton (ofType)
open Paper.Extension.Singleton.ThreeCycle (step partialFold)

universe u v w
variable {κ : Type u} [AtomValues κ] {Φ : Type v} [HasTy Φ (Ty κ)]
  {ε : Type w} [HasEff Φ ε] (pe : ε)

local notation "Obj" => ofType (JoinedStep (τ := Ty κ) (Φ := Φ) pe)
local notation "Val" => Ty.denote (AtomValues.carrier (κ := κ))

/-- For an inhabited retained type, none of the three partial folds of
the repeat-only cycle admits a first commuting square in BinaryFold. -/
theorem no_partial_fold_on_repeat {A : Ty κ} (a : Val A) (keep : Fin 3)
    (next : Obj A ⨿ Obj A ⟶ Obj A ⨿ (Obj A ⨿ Obj A)) :
    step (coprod.inr : Obj A ⟶ Obj A ⨿ Obj A) ≫ coprod.map (𝟙 (Obj A)) (partialFold (Obj A) keep) ≠
      partialFold (Obj A) keep ≫ next :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldThreeCycle.no_partial_fold_on_repeat
    pe a keep next

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold
