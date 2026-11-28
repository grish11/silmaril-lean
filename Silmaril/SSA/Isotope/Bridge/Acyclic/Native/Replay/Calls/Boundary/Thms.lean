module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Boundary.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Native.Replay.CallsBoundary

/-! # Exact computed-call and effectful-pair replay boundaries -/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural Native.CallBoundary

/-- The original two-call witness now replays at its exact typed endpoints. -/
theorem CallBoundary.repaired : nestedEndpoint.CallEqv sequencedEndpoint :=
  repaired_proof

namespace CallPairBoundary

open Region.Paper.BoundSimulation.Obstruction.PairSequencing.CallPair (U Packet left_typed right_typed)
open CallBoundary (input)

/-- Effectful pair sequencing is valid and remains separated by the computed-call relation. -/
theorem separation : paired.Valid sequenced ∧ ¬ paired.CallEqv sequenced :=
  ⟨valid_pair_proof, independent_pair_proof⟩

/-- These exact LetCase derivations use pair eta followed by ordered pair beta. -/
theorem letCase_pair :
    LetCase.LocallyNameless.Equiv false LetCase.Structural.Reply.Γ₀ input
      pairCode.toLetCase.1 seqCode.toLetCase.1 Packet :=
  letCase_pair_proof

/-- The computed-call relation also separates the exact guarded reifications. -/
theorem reify_pair_fails :
    ¬ Region.Paper.WithComputedCallReturns.ConstructorJoin.Eqv false input.toList
      ((Code.ofLetCase pairCode.toLetCase.2).guardedSSA 0) ((Code.ofLetCase seqCode.toLetCase.2).guardedSSA 0)
      [Packet] :=
  reify_pair_fails_proof

/-- The missing equation is the existing unrestricted ordered pair step. -/
theorem pair_step : Region.Paper.WithPairReturns.Step [U] paired.region sequenced.region [Packet] :=
  .seq left_typed right_typed

/-- The ordered-pair extension replays the exact witness separated by
the computed-call relation. -/
theorem pair_repaired : paired.PairCallEqv sequenced :=
  .extra paired.typed sequenced.typed (.inr pair_step)

/-- The same repair connects the actual guarded reifications. -/
theorem reify_pair_repaired :
    Region.Paper.WithComputedCallReturns.OrderedPairs.Eqv false input.toList
      ((Code.ofLetCase pairCode.toLetCase.2).guardedSSA 0)
      ((Code.ofLetCase seqCode.toLetCase.2).guardedSSA 0) [Packet] :=
  reify_pair_repaired_proof pair_repaired

end CallPairBoundary
end Silmaril.Isotope.LambdaSSA.Acyclic.Native
