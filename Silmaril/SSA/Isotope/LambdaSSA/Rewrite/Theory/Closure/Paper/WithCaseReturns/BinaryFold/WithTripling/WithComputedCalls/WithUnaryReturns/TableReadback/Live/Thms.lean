module

public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live.Defs
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.LiveTable
import Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.Trace

/-! # Reachable local feedback separates the written table and readback -/

public section

namespace Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live

open Silmaril.Isotope.LambdaSSA

/-- The exact concrete readback equation fails in the unchanged quotient.
The observer distinguishes endless two-row local feedback from endless
one-row dispatcher feedback, while preserving the existing equations. -/
theorem readback_fails : ¬ Readback false labels entry_typed rows_typed :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.LiveTable.readback_fails

/-- The same live table also separates the packed dispatcher when the entry
is already a single constructor branch. -/
theorem constructorEntry_readback_fails :
    ¬ Readback false labels
      (.br (ℓ := 0) rfl (.var (i := 0) rfl : Tm.BranchValue [Payload] (.var 0 : Tm Op) Payload))
      rows_typed :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.BoundSimulation.Obstruction.PairSequencing.LiveTable.constructorEntry_readback_fails

/-- The written source requests an initial payload, polls, takes the
backedge and polls the restored capture before returning the ordered sum. -/
theorem written_trace (x y z : Nat) :
    Semantics.Region.Eval Replies (fun _ => .atom x) written [] 0
      (.inr (.pair (.atom x) (.atom z))) [.enter, .poll, .poll] :=
  Silmaril.Proofs.SSA.Isotope.LambdaSSA.Rewrite.Paper.TriplingWithUnaryReturns.LiveTable.written_trace x y z

end Silmaril.Isotope.LambdaSSA.Region.Paper.WithCaseReturns.BinaryFold.WithTripling.WithComputedCalls.WithUnaryReturns.TableReadback.Live
