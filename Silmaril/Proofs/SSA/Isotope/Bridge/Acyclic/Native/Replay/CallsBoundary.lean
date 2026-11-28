module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Boundary.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Calls.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.OrderedPairs.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.CallPair.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.UnaryReturn.Thms

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region.Paper
open WithComputedCallReturns
open Region.Paper.BoundSimulation.Obstruction.PairSequencing
open RawBranch (Op)
open LetCase.LocallyNameless (Equiv HasType)
open LetCase.Structural.Reply (Γ₀)
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural Native.CallBoundary

set_option backward.isDefEq.respectTransparency false

theorem CallBoundary.repaired_proof : nestedEndpoint.CallEqv sequencedEndpoint := by
  have a := CallOperand.argument_typed
  have b : Tm.HasType (U :: [U]) (.op Op.call (.var 0)) U := .op (.var rfl)
  have source := UnaryReturn.returnRegion_eq_returnOnce (Seed := ConstructorJoin.Seed false)
    (fun e => .inl (.inl (.inr (.inl e)))) (Tm.HasType.op (f := Op.call) a)
  have target := UnaryReturn.returnRegion_eq_returnOnce (Seed := ConstructorJoin.Seed false)
    (fun e => .inl (.inl (.inr (.inl e)))) (Tm.HasType.let₁ a b)
  exact source.symm.trans ((ConstructorJoin.ofCall (.seq Op.call a)).trans target)

namespace CallPairBoundary

open CallPair (U Packet)
open CallBoundary (input)

theorem letCase_pair_proof : Equiv false Γ₀ input pairCode.toLetCase.1 seqCode.toLetCase.1 Packet := by
  have l : HasType Op Γ₀ input (.op .call (.bv 0)) U := .op .bv
  have r : HasType Op Γ₀ input (.let₁ (.bv 0) (.bv 0)) U := .let₁ .bv .bv
  have parts : HasType Op Γ₀ ((input.snoc U).snoc U) (.pair (.bv 1) (.bv 0)) Packet := .pair .bv .bv
  exact (Equiv.letEta (.pair l r)).trans ((Equiv.pairEta (.pair l r)).symm.trans (Equiv.pairBeta l r parts))

theorem valid_pair_proof : paired.Valid sequenced :=
  @Endpoint.valid_of_code_equiv Op _ 1 input Packet paired sequenced pairCode seqCode rfl rfl letCase_pair_proof

theorem independent_pair_proof : ¬ paired.CallEqv sequenced :=
  CallPair.separation

private theorem roundTrip (p : Endpoint Op input Packet) (code : Code Op input Packet)
    (written : code.toSSA 0 = p.region) (admitted : code.Admitted)
    (guarded : Region.ValueBranches input.toList p.region [Packet]) :
    ConstructorJoin.Eqv false input.toList p.region
      ((Code.ofLetCase code.toLetCase.2).guardedSSA 0) [Packet] :=
  ConstructorJoin.ofConstructor (WithConstructorSequencing.Joined.ofJoined
    (p.joined_roundTrip_at code written admitted guarded))

private theorem pairRoundTrip :
    ConstructorJoin.Eqv false input.toList paired.region
      ((Code.ofLetCase pairCode.toLetCase.2).guardedSSA 0) [Packet] :=
  roundTrip paired pairCode rfl ⟨trivial, trivial⟩
    (.let₁ (.pair CallPair.left_typed CallPair.right_typed) (.br rfl (.var rfl)))

private theorem seqRoundTrip :
    ConstructorJoin.Eqv false input.toList sequenced.region
      ((Code.ofLetCase seqCode.toLetCase.2).guardedSSA 0) [Packet] :=
  roundTrip sequenced seqCode rfl ⟨trivial, ⟨trivial, trivial⟩, trivial⟩
    (WithPairReturns.pairSequence_typed CallPair.left_typed CallPair.right_typed)

theorem reify_pair_fails_proof :
    ¬ ConstructorJoin.Eqv false input.toList
      ((Code.ofLetCase pairCode.toLetCase.2).guardedSSA 0) ((Code.ofLetCase seqCode.toLetCase.2).guardedSSA 0)
      [Packet] := fun h => independent_pair_proof (pairRoundTrip.trans (h.trans seqRoundTrip.symm))

theorem reify_pair_repaired_proof (h : paired.PairCallEqv sequenced) :
    OrderedPairs.Eqv false input.toList
      ((Code.ofLetCase pairCode.toLetCase.2).guardedSSA 0) ((Code.ofLetCase seqCode.toLetCase.2).guardedSSA 0)
      [Packet] :=
  (OrderedPairs.ofCalls pairRoundTrip).symm.trans (h.trans (OrderedPairs.ofCalls seqRoundTrip))

end CallPairBoundary
end Silmaril.Isotope.LambdaSSA.Acyclic.Native
