module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Boundary.Defs
public import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Boundary.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Boundary.Thms
import Silmaril.SSA.Isotope.Bridge.Acyclic.Native.Replay.Constructor.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithConstructorSequencing.Joined.Thms
import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.BoundSimulation.Obstruction.PairSequencing.CallOperand.Thms
public import Silmaril.SSA.Isotope.LambdaSSA.Rewrite.Theory.Closure.Paper.WithComputedCallReturns.Defs

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Native

open Region.Paper
open scoped LetCase.Structural.Finite LetSeq.StraightLine.Structural Native.Boundary

theorem pair_repaired_proof : Boundary.paired.ConstructorEqv Boundary.sequenced :=
  .extra Boundary.paired.typed Boundary.sequenced.typed (.inr Boundary.pair_constructor_step)

theorem unit_repaired_proof : Boundary.unitReturn.ConstructorEqv Boundary.unitForward :=
  WithConstructorSequencing.Joined.ofJoined Boundary.unit_joined

namespace CallBoundary

open Region.Paper.BoundSimulation.Obstruction.PairSequencing
open Region.Paper.BoundSimulation.Obstruction.PairSequencing.RawBranch (Op)
open LetCase.LocallyNameless (Equiv HasType)
open LetCase.Structural.Reply (Γ₀)
open scoped Native.CallBoundary

set_option backward.isDefEq.respectTransparency false

/-- The very same call-argument split used in the finite normalization. -/
theorem bindOp_proof : Equiv false Γ₀ input nested.1 sequenced.1 U := by
  have ha := argument.2.toHasType
  have slot : HasType Op Γ₀ (input.snoc U) (.bv 0) U := .bv
  have call : HasType Op Γ₀ (input.snoc U) (.op .call (.bv 0)) U := .op slot
  exact ((Equiv.letEta (.op (f := Op.call) ha)).symm.trans (Equiv.bindOp ha (HasType.bv (ι := 0)))).trans
    (Equiv.let₁ (.refl ha) (Equiv.letEta call))

theorem separate_proof : ¬ nestedEndpoint.ConstructorEqv sequencedEndpoint :=
  CallOperand.separation

theorem valid_proof : nestedEndpoint.Valid sequencedEndpoint := by
  let l : Code Op input U := .let₁ nested (.br ⟨.bv 0, .bv⟩)
  let r : Code Op input U := .let₁ sequenced (.br ⟨.bv 0, .bv⟩)
  have lhs : l.toSSA 0 = nestedEndpoint.region := rfl
  have rhs : r.toSSA 0 = sequencedEndpoint.region := rfl
  have eq : Equiv false Γ₀ input l.toLetCase.1 r.toLetCase.1 U :=
    .let₁ bindOp_proof (.refl .bv)
  exact @Endpoint.valid_of_code_equiv Op _ 1 input U nestedEndpoint sequencedEndpoint l r lhs rhs eq

theorem reification_fails_proof : ¬ ConstructorReplay nested sequenced := by
  intro replay
  have left := operand_roundTrip_constructor false nested trivial
  have right := operand_roundTrip_constructor false sequenced ⟨⟨trivial, trivial⟩, trivial⟩
  exact separate_proof (left.trans ((replay bindOp_proof).trans right.symm))

theorem computedCall_proof :
    WithComputedCallReturns.Step [U]
      (Region.CfgEta.TypeCategory.returnRegion CallOperand.nested)
      (Region.CfgEta.TypeCategory.returnRegion CallOperand.sequenced) [U] :=
  .seq Op.call CallOperand.argument_typed

end CallBoundary
end Silmaril.Isotope.LambdaSSA.Acyclic.Native
