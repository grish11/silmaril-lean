module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.ThreeCycle.MatrixBoundary.Binary.Defs
public import Mathlib.Logic.Equiv.Prod

/-! # Feedback matrices with an unchanged context -/

@[expose] public section

namespace Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary

/-- Carry the original context into the selected outward or recursive branch.
Rows and columns use the coordinates of product distributing over sum. -/
def contextual {C I X E : Type} [DecidableEq C] (f : C → (I ⊕ X) → (E ⊕ X) → Scalar) :
    ((C × I) ⊕ (C × X)) → ((C × E) ⊕ (C × X)) → Scalar := fun i j =>
  let (ci, ri) := (Equiv.prodSumDistrib C I X).symm i
  let (cj, rj) := (Equiv.prodSumDistrib C E X).symm j
  if ci = cj then f ci ri rj else 0

end Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary
