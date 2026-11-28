module

public import Silmaril.SSA.Peggy.Worked.StrengthReduction.Defs
public import Silmaril.SSA.PEG.Semantics.Thms
import Silmaril.Proofs.SSA.Peggy.Worked.StrengthReduction.Recurrence
import Silmaril.Proofs.SSA.Peggy.Worked.StrengthReduction.Context

public section

namespace Silmaril.SSA.Peggy.Worked.StrengthReduction

open PEG
open RVSDG (Tuple)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat} {g : Graph P params results n l}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params} {values : g.Valuation m}
variable {site : Fin n} {ops : Profile P}

theorem Match.target_theta (found : Match g site ops) :
    Rules.HasNode (g := found.candidate) found.resultRef (.theta found.loop) found.thetaArgs :=
  Silmaril.Proofs.SSA.Peggy.Worked.StrengthReduction.target_theta found

theorem Match.target_other (found : Match g site ops) (i : Fin (n + 1))
    (different : found.resultRef.id ≠ i) : found.candidate.node i = found.added.append.node i :=
  Silmaril.Proofs.SSA.Peggy.Worked.StrengthReduction.target_other found i different

/-- For the actual matched node equations, scaling a θ recurrence gives
the folded initial value and the additive step on the preceding scaled value. -/
theorem scaled_recurrence (solves : g.Solves m env values) (law : Law m ops)
    {scaled factor counter initial update bump : Ref g.sort .count} {loop : Fin l}
    (scaleNode : Rules.HasNode scaled (.op ops.scale) (.cons factor (.cons counter .nil)))
    (factorNode : Rules.HasNode factor (.op ops.factor) .nil)
    (thetaNode : Rules.HasNode counter (.theta loop) (.cons initial (.cons update .nil)))
    (baseNode : Rules.HasNode initial (.op ops.base) .nil)
    (stepNode : Rules.HasNode update (.op ops.step) (.cons counter .nil))
    (bumpNode : Rules.HasNode bump (.op ops.add) (.cons factor (.cons scaled .nil)))
    (i : Index l) :
    Rules.readRef values scaled i =
      match i loop with
      | 0 => Rules.readRef values initial i
      | k + 1 => Rules.readRef values bump (i.set loop k) :=
  Silmaril.Proofs.SSA.Peggy.Worked.StrengthReduction.scaled_recurrence solves law
    scaleNode factorNode thetaNode baseNode stepNode bumpNode i

/-- The native streams in the appended source solve the actual target,
including the new feedback cycle and every retained surrounding node. -/
theorem Match.lifted_solution (found : Match g site ops) (law : Law m ops)
    {vals : found.added.append.Valuation m}
    (solves : found.added.append.Solves m env vals) : found.candidate.Solves m env vals :=
  Silmaril.Proofs.SSA.Peggy.Worked.StrengthReduction.lifted_solution found law solves

/-- The independent rank check admits the rewritten graph. Exact overlap
between the partial streams includes all iteration indices and bottom. -/
theorem Match.candidate_sound (found : Match g site ops) (law : Law m ops)
    (before : WellFounded g.Demand) (rank : DemandRank (n + 1) l)
    (checked : rank.check found.candidate = true) (idx : Index l) :
    g.observe m (g.denote m env before) idx =
      found.candidate.observe m (found.candidate.denote m env
        (found.candidate.demandWellFounded_of_check rank checked)) idx :=
  Silmaril.Proofs.SSA.Peggy.Worked.StrengthReduction.rewrite_sound found law before
    (found.candidate.demandWellFounded_of_check rank checked) idx

end Silmaril.SSA.Peggy.Worked.StrengthReduction
