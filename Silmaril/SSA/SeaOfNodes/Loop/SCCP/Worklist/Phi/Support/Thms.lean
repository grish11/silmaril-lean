module

public import Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support.Correctness

/-! Agreement of abstract reads on the carried support of a ranked wire. -/

public section

namespace Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support

open Diamond (Dataflow Model Signature Ty ValueSort dataPorts)
open Diamond.SCCP (Fact evalFacts readLocal)
open RVSDG (Origin Tuple extend)

universe u v w

variable {Data : Type u} {Op : Signature.{u, v} Data} {m : Model.{u, v, w} Op}
variable {inputs carried : List (ValueSort Data)} {sigs : List (List (Ty Data))} {t : Ty Data}

/-- Changing carried facts outside the wire's transitive operand support
leaves its abstract read unchanged under the same captured facts. -/
theorem wire_agrees (flow : Dataflow Op (Loop.headerPorts inputs carried) [] sigs)
    (origin : Origin (Loop.headerPorts inputs carried) (extend [] sigs) t)
    (input : Tuple (Fact m.value) (dataPorts inputs))
    {left right : BankFacts m.value (dataPorts carried)}
    (same : ∀ i ∈ wire (inputs := inputs) (carried := carried) flow origin, left i = right i) :
    let leftArgs := appendTuple (bankTuple left) input
    let rightArgs := appendTuple (bankTuple right) input
    readLocal leftArgs (evalFacts m leftArgs flow PUnit.unit) origin =
      readLocal rightArgs (evalFacts m rightArgs flow PUnit.unit) origin :=
  Proofs.wire_agrees flow origin input same

/-- The masked watch keys compare exactly the facts at supported coordinates. -/
theorem restrictBank_eq_iff {value : Data → Type w} {ports : List (Ty Data)}
    (support : Finset (Fin ports.length)) {left right : BankFacts value ports} :
    restrictBank support left = restrictBank support right ↔ ∀ i ∈ support, left i = right i :=
  Proofs.restrictBank_eq_iff support

end Silmaril.SSA.SeaOfNodes.Loop.SCCP.Worklist.Phi.Support
