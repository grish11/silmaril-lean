module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.StructuralValues.ThreeCycle.MatrixBoundary.Binary.Context.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrixContext

/-! # Feedback elimination in distributed context coordinates -/

public section

namespace Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary

/-- Eliminating a recursive packet changes only its own context block.
This allows the retained row and exit weights to depend on the context. -/
theorem eliminate_contextual {C I X E : Type} [DecidableEq C]
    (f : C → (I ⊕ X) → (E ⊕ X) → Scalar) (c : C) (x : X) :
    eliminate (c, x) (contextual f) =
      contextual (Function.update f c (eliminate x (f c))) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrixContext.eliminate_contextual f c x

/-- Along any elimination schedule, each context observes precisely the
subsequence of recursive states in its own context block. -/
theorem contextual_schedule {C I X E : Type} [DecidableEq C]
    (f : C → (I ⊕ X) → (E ⊕ X) → Scalar) (states : List (C × X)) :
    states.foldr eliminate (contextual f) =
      contextual (fun c =>
        (states.filterMap (fun s => if s.1 = c then some s.2 else none)).foldr eliminate (f c)) :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BinaryFoldBitMatrixContext.contextual_schedule f states

end Silmaril.Calco2019.CounterSemiring.ThreeCycle.Binary
