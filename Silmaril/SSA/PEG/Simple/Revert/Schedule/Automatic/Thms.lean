module

public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Defs
public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.Schedule.Automatic.Laws

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {roles : Roles P} {rank : DemandRank n l}
variable {m : Interpretation.{u,v,w} P}
variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]

/-- Success carries the exact original-graph checker equation, including
the proposed plan, parameter rows, and rank. -/
theorem discover_checked {leaves : List (Leaf roles)} {budget : Nat} {a : Found g roles rank}
    (_found : discover g roles rank leaves budget = .ok a) :
    Schedule.check g a.plan a.inputs rank = some a.gate :=
  a.checked

theorem Found.laws (a : Found g roles rank) (model : roles.Laws m) : a.gate.val.plan.Laws m :=
  a.gate.property.symm ▸ Proofs.planLaws a.plan a.roleMatch model

/-- A running discovered plan returns the original ordered PEG roots and
certifies its first exits and typed boundaries. -/
theorem Found.observations_of_exec (a : Found g roles rank) (model : roles.Laws m)
    (input : Tuple m.Value params) (base : Index l) {output : Tuple m.Value results}
    (ran : Exec m a.gate.val.plan.revert input (some output)) :
    let values := g.denote m input a.gate.val.demandWellFounded
    a.gate.val.plan.Observations m values base g.roots output ∧
      g.observe m values base = output.map (fun _ => some) :=
  a.gate.val.observations_of_exec (a.laws model) input base ran

/-- Under the same slice-definedness premises as Schedule, finite
first-exit observations also construct a run of the discovered plan. -/
theorem Found.exec_iff_observations (a : Found g roles rank) (model : roles.Laws m)
    (input : Tuple m.Value params) (base : Index l) (output : Tuple m.Value results)
    (slices : a.gate.val.plan.Slices m (g.denote m input a.gate.val.demandWellFounded) base) :
    Exec m a.gate.val.plan.revert input (some output) ↔
      a.gate.val.plan.Observations m (g.denote m input a.gate.val.demandWellFounded) base g.roots output :=
  a.gate.val.exec_iff_observations (a.laws model) input base output slices

end Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic
