module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Example.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedProductProducers.Intrinsic.SumCase.Tree.Thms
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseTreeExample

/-! # A native two-level case and its visible execution -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.Example

open Silmaril Silmaril.Isotope Silmaril.Isotope.LambdaSSA
open Semantics.Categorical Semantics.Interaction.Typed
open Silmaril.Isotope.LetIter.ProofRelevant.Semantics.Categorical (typeJ)
open CategoryTheory
open SumCase.Example (Atom Payload PayloadValue Model Op)

attribute [local instance] typeModel categoricalInstructions

local notation "J" => typeJ (m := Model)
local notation "M" => ofMonadicTypeModel (τ := Ty Atom)

/-- Both levels are literal cases. The nested discriminator reads the first
reply. Its left arm can still reach the original input. -/
theorem literal_cases :
    nested.elaborate.val =
      .case (.op Op.choose (.var 0))
        (.case (.op Op.choose (.let₂ (.pair (.var 1) (.var 0)) (.var 0)))
          (.let₁ (.let₂ (.pair (.pair (.var 2) (.var 1)) (.var 0)) (.var 1))
            (.let₁ (.let₂ (.var 0) (.var 1)) (.br 1 (.var 0))))
          (.let₁ (.let₂ (.pair (.pair (.var 2) (.var 1)) (.var 0)) (.var 0))
            (.br 0 (.var 0))))
        (.let₁ (.let₂ (.pair (.var 1) (.var 0)) (.var 0)) (.br 1 (.var 0))) :=
  rfl

/-- On a left reply the second discriminator receives that reply, and the
left leaf can still return the original input. The outer right branch returns
directly. -/
theorem visible_elaboration (x : PayloadValue) :
    ∃ f, RegionDenotes J M nested.elaborate.property.hasType f ∧
      f.of (PUnit.unit, x) = expected x :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.SelectedCaseTreeExample.visible_elaboration x

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithComputedProductProducers.Intrinsic.CaseTree.Example
