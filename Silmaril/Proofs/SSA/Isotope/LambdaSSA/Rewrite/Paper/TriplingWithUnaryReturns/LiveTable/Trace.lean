module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live.Defs

public section

namespace Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable

open Silmaril.Isotope.LambdaSSA
open Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live

/-- Execute the original written graph through row zero, row one, row zero,
and then its outward exit. -/
theorem written_trace (x y z : Nat) :
    Semantics.Region.Eval Replies (fun _ => .atom x) written [] 0
      (.inr (.pair (.atom x) (.atom z))) [.enter, .poll, .poll] := by
  refine .cfg (first := 0) (.let₁ (.op .var (.entry x y)) (.br .var)) ?_
  refine .step (next := 1) (by decide) (.let₁ (.op .var (.repeat y)) (.case_inl .var (.br .var))) ?_
  refine .step (next := 0) (by decide) (.br .var) ?_
  refine .step (next := 2) (by decide) (.let₁ (.op .var (.exit x z)) (.case_inr .var (.br (.inr (.pair .var .var))))) ?_
  exact .exit (by decide)

end Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable
