module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedSumCaseExample

/-! # Execution and annotation regressions for a selected case -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.SumCase.Example

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Semantics.Categorical Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open Silmaril.Elgot.ITree CategoryTheory
open scoped MonoidalCategory

attribute [local instance] typeModel categoricalInstructions

local notation "J" => typeJ (m := Model)
local notation "M" => ofMonadicTypeModel (τ := Ty Atom)

theorem nativeCase :
    program.elaborate.val =
      .case (.op .choose (.var 0))
        (.let₁ (.op .left (.pair (.var 1) (.var 0))) (.br 1 (.var 0)))
        (.let₁ (.op .right (.pair (.var 1) (.var 0))) (.br 0 (.var 0))) :=
  rfl

/-- The two exits have the same payload type and distinct outward tags. -/
theorem distinctSlots (left right : Nat) : exit1 left ≠ exit0 right :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedSumCaseExample.distinctSlots left right

/-- The exact elaborated region emits the discriminator event, then the
selected arm event with the retained input and the chosen payload. -/
theorem visibleElaboration (x : PayloadValue) :
    ∃ f, RegionDenotes J M program.elaborate.property.hasType f ∧
      f.of (PUnit.unit, x) = expected x :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedSumCaseExample.visibleElaboration x

namespace Typing

theorem sameErasure :
    (annotated .plain).elaborate.val = (annotated .marked).elaborate.val := rfl

theorem differentAnnotations : annotated .plain ≠ annotated .marked := by
  intro h
  cases (congrArg SumCase.rightType h : Annotation.plain = Annotation.marked)

end Typing

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.SumCase.Example
