module

public import Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Defs
import Silmaril.Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.Correctness

public section

namespace Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch

open Pure.SubZero (model)
open RVSDG (Tuple)

variable {inputs : List (ValueSort Unit)} {sigs : List (List (Ty Unit))}
variable {g : AddPhi.Pair.Source inputs sigs} {x : InputWord inputs} {result : Result inputs sigs}

/-- Exact admission and output, with the result constructor and native
program determined by the two checked predecessor sums. -/
theorem rewrite_eq_ok_iff :
    rewrite g x = .ok result ↔
      ∃ first second, AddPhi.Pair.literalRows? g = some (first, second) ∧
        AddPhi.Pair.nonconstantColumns first second = true ∧
        result = emit g x first second :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.rewrite_eq_ok_iff

/-- All three emitted shapes preserve and reflect the nominated finite return. -/
theorem rewrite_returns_iff (accepted : rewrite g x = .ok result)
    (entry : Tuple (Val model.value) (dataPorts inputs)) (value : BitVec 64) :
    result.Returns entry value ↔ (original g x).Returns entry value :=
  Proofs.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch.rewrite_returns_iff accepted entry value

end Silmaril.SSA.SeaOfNodes.Diamond.AddPhi.Rotate.Pair.Dispatch
