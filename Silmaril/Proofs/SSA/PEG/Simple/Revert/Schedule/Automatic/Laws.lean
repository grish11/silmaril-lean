module

public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Defs

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Proofs

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results args outs : List (Ty Data)} {n l rows loops : Nat}
variable {g : Graph P params results n l} {localGraph : Graph P args outs rows loops}
variable {roles : Roles P} {m : Interpretation.{u,v,w} P}

private theorem regionLaws (r : Region localGraph) (checked : RegionRoles roles r)
    (model : roles.Laws m) : r.Laws m := by
  cases r with
  | closed a =>
    cases roles with
    | nestedOnly _ => exact False.elim checked
    | counted roles =>
      obtain ⟨zero, tick, negate⟩ := checked
      have model : roles.Laws m := model
      exact ⟨zero.symm ▸ model.zero, tick.symm ▸ model.tick, negate.symm ▸ model.negate⟩
  | nested a =>
    have negate : a.descriptor.negate = roles.negate := checked
    intro b
    rw [negate]
    cases roles with
    | counted roles => exact (show roles.Laws m from model).negate b
    | nestedOnly _ => exact model b

theorem planLaws (p : Plan g args outs) (checked : PlanRoles roles p) (model : roles.Laws m) : p.Laws m := by
  induction p with
  | done _ => trivial
  | step _ stage tail ih =>
    have rolesMatch : RegionRoles roles stage.region ∧ PlanRoles roles tail := checked
    exact ⟨regionLaws stage.region rolesMatch.1 model, ih rolesMatch.2⟩

end Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Proofs
