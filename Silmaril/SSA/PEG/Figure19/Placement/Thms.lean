module

public import Silmaril.SSA.PEG.Figure19.Placement.Defs
public import Silmaril.SSA.PEG.Figure19.Thms
import Silmaril.Proofs.SSA.PEG.Figure19.Placement.Correctness

public section

namespace Silmaril.SSA.PEG.Figure19

universe u v w

open RVSDG (Tuple)

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {depth : Fin l → Nat}
variable {direction : EvalDirection} {cap : Nat} {ctx : Assumptions n} {i target : Fin n}

theorem StrictPath.derives (path : StrictPath g target i)
    (typed : Derives g depth direction cap ctx i) : Derives g depth direction cap ctx target :=
  Placement.Proofs.derives path typed

theorem Derives.phiArms (typed : Derives g depth direction cap ctx i)
    {flag : Ref g.sort .bool} {yes no : Ref g.sort (g.sort i)}
    (row : g.node i = .ofLabel .phi (.cons flag (.cons yes (.cons no .nil)))) :
    Derives g depth direction cap ctx yes.id ∧ Derives g depth direction cap ctx no.id :=
  Placement.Proofs.phiArms typed row

/-- A strict dependency on θ gives a lower bound on placement depth,
even in the presence of Type-Reduce and θ assumptions. -/
theorem StrictPath.depth_le (path : StrictPath g target i)
    (typed : Derives g depth direction cap ctx i) {key : Fin l}
    (theta : (g.node target).label.thetaLoop = some key) : depth key ≤ cap :=
  Placement.Proofs.depth_le path typed theta

/-- A defined strict use forces the dependency to be defined at the same
iteration, without assuming primitive totality. -/
theorem StrictPath.defined (path : StrictPath g target i)
    {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params}
    {values : g.Valuation m} {idx : Index l} (solves : g.Solves m env values)
    (start : (values (i, idx)).isSome) : (values (target, idx)).isSome :=
  Placement.Proofs.defined path solves start

/-- A defined φ requires its condition and a defined selected operand at the same index. -/
theorem phi_demands {args : Tuple (Ref g.sort) [.bool, g.sort i, g.sort i]}
    (row : g.node i = .ofLabel .phi args)
    {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params}
    {values : g.Valuation m} {idx : Index l} (solves : g.Solves m env values)
    (start : (values (i, idx)).isSome) :
    (values ((args.get .head).id, idx)).isSome ∧
      ((values ((args.get (.tail .head)).id, idx)).isSome ∨
       (values ((args.get (.tail (.tail .head))).id, idx)).isSome) :=
  Placement.Proofs.phi_demands row solves start

/-- A row strictly used by both arms of a defined φ is already demanded.
This justifies sharing it before the choice for partial primitives. -/
theorem StrictPath.defined_of_phi {flag : Ref g.sort .bool} {yes no : Ref g.sort (g.sort i)}
    (row : g.node i = .ofLabel .phi (.cons flag (.cons yes (.cons no .nil))))
    (trueUse : StrictPath g target yes.id) (falseUse : StrictPath g target no.id)
    {m : Interpretation.{u,v,w} P} {env : Tuple m.Value params}
    {values : g.Valuation m} {idx : Index l} (solves : g.Solves m env values)
    (start : (values (i, idx)).isSome) : (values (target, idx)).isSome :=
  Placement.Proofs.defined_of_phi row trueUse falseUse solves start

end Silmaril.SSA.PEG.Figure19
