module

public import Silmaril.SSA.Peggy.Worked.EvalScale.Defs
public import Silmaril.SSA.Peggy.EPEG.Saturation.Extension.Thms
public import Silmaril.SSA.Peggy.EPEG.Selection.Thms
import Silmaril.Proofs.SSA.Peggy.Worked.EvalScale.Rule
import Silmaril.Proofs.SSA.Peggy.Worked.EvalScale.Replay

public section

namespace Silmaril.SSA.Peggy.Worked.EvalScale

open PEG
open RVSDG (Tuple)
open EPEG.Saturation.Extension (State)

universe u v x

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {s : State P params results n l} {site : Fin n}
variable {m : Interpretation.{u,v,x} P} {env : Tuple m.Value params} {values : g.Valuation m}
variable {factor : P [] .count} {op : P [.count, .count] .count}

theorem binary_at (solves : g.Solves m env values) {r a b : Ref g.sort .count}
    (node : Rules.HasNode r (.op op) (.cons a (.cons b .nil))) (i : Index l) :
    Rules.readRef values r i = (Rules.readRef values a i).bind fun left =>
      (Rules.readRef values b i).bind fun right => m.run op (.cons left (.cons right .nil)) :=
  Silmaril.Proofs.SSA.Peggy.Worked.EvalScale.binary_at solves node i

/-- Appendix A.1 push-through-eval under a defined invariant left operand
and a model that cannot introduce new bottom in the sampled prefix. -/
theorem commute (solves : g.Solves m env values)
    {outer sampled inner target a stream count : Ref g.sort .count} {loop : Fin l}
    (src : Rules.HasNode outer (.op op) (.cons a (.cons sampled .nil)))
    (sample : Rules.HasNode sampled (.eval loop) (.cons stream (.cons count .nil)))
    (product : Rules.HasNode inner (.op op) (.cons a (.cons stream .nil)))
    (dst : Rules.HasNode target (.eval loop) (.cons inner (.cons count .nil)))
    (k : m.Value .count) (constant : ∀ i, Rules.readRef values a i = some k)
    (total : ∀ b : m.Value .count, (m.run op (.cons k (.cons b .nil))).isSome) :
    Rules.StreamEq values outer target :=
  Silmaril.Proofs.SSA.Peggy.Worked.EvalScale.commute solves src sample product dst k constant total

theorem Match.equation_holds (found : Match s.graph site factor op)
    (law : Law m factor op) {streams : found.outside.append.Valuation m}
    (solves : found.outside.append.Solves m env streams) : found.equation.Holds streams :=
  Silmaril.Proofs.SSA.Peggy.Worked.EvalScale.equation_holds found law solves

theorem Match.plan_holds (found : Match s.graph site factor op) (law : Law m factor op) :
    found.plan.Holds env 2 :=
  Silmaril.Proofs.SSA.Peggy.Worked.EvalScale.plan_holds found law

theorem Match.equates (found : Match s.graph site factor op) :
    found.saturated.classes found.oldResult.id = found.saturated.classes found.outside.fresh.id :=
  Silmaril.Proofs.SSA.Peggy.Worked.EvalScale.equates found

theorem Match.check_of_rank (found : Match s.graph site factor op) (rank : DemandRank (n + 2) l)
    (ranked : rank.check found.extract = true) : found.checkExtraction rank = true :=
  Silmaril.Proofs.SSA.Peggy.Worked.EvalScale.check_of_rank found rank ranked

/-- Native replay and the independent root/row/rank certificate preserve
every ordered partial observation, including repeated root occurrences. -/
theorem Match.extract_sound (found : Match s.graph site factor op) (wf : WellFounded s.graph.Demand)
    (valid : s.classes.Valid (s.graph.denote m env wf)) (law : Law m factor op)
    (rank : DemandRank (n + 2) l) (checked : found.checkExtraction rank = true) (i : Index l) :
    s.graph.observe m (s.graph.denote m env wf) i =
      found.extract.observe m (found.extract.denote m env
        ((found.selection rank).demandWellFounded (Bool.and_eq_true_iff.mp checked).1)) i :=
  Silmaril.Proofs.SSA.Peggy.Worked.EvalScale.extract_sound found wf valid law rank checked i

end Silmaril.SSA.Peggy.Worked.EvalScale
