module

public import Silmaril.SSA.PEG.Figure19.Placement.MustEval.Defs
public import Silmaril.SSA.PEG.Figure19.Placement.Thms
import Silmaril.Proofs.SSA.PEG.Figure19.Placement.MustEval.Correctness

public section

namespace Silmaril.SSA.PEG.Figure19.MustEval

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {i target : Fin n}
variable {m : Interpretation.{u,v,w} P} {env : RVSDG.Tuple m.Value params}
variable {values : g.Valuation m} {idx : Index l}

/-- Every computed demand is defined when its root is defined at the same
index and input. Primitive interpretations may be partial. Rank is needed
to obtain the repaired Figure 11 solution, independently of this theorem. -/
theorem defined (solves : g.Solves m env values) (fuel : Nat)
    (hit : target ∈ (rounds g fuel)[i.val]) (root : (values (i, idx)).isSome) :
    (values (target, idx)).isSome :=
  Proofs.sound solves fuel hit root

/-- Once the number of synchronous rounds exceeds the local rank, one
more transfer leaves that row's computed set unchanged. -/
theorem stable {rank : Fin n → Nat} (ranked : Ranked g rank) (fuel : Nat)
    (within : rank i < fuel) : (rounds g (fuel + 1))[i.val] = (rounds g fuel)[i.val] :=
  Proofs.stable ranked fuel within

end Silmaril.SSA.PEG.Figure19.MustEval
