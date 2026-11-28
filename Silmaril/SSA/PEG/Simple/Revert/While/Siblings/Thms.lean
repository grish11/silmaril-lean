module

public import Silmaril.SSA.PEG.Simple.Revert.While.Siblings.Defs
public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Siblings.Correspondence

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Siblings

open RVSDG (Tuple)
open Simple.Revert.While.Region

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params intermediate args results carried₁ carried₂ : List (Ty Data)} {n n₁ n₂ : Nat}
variable {g : Graph P params results n 2}
variable {left : Graph P params intermediate n₁ 1} {right : Graph P args results n₂ 1}
variable {first : Closed.Accepted left carried₁} {second : Closed.Accepted right carried₂}
variable {m : Interpretation.{u,v,w} P}

theorem Accepted.demandWellFounded (a : Accepted g first second) : WellFounded g.Demand :=
  g.demandWellFounded_of_check a.rank a.ranked

/-- One actual sequential SIMPLE run fixes the original PEG observations
at both least passes, including the ordered intermediate bundle. -/
theorem Accepted.observations_of_exec (a : Accepted g first second)
    (laws₁ : first.Laws m) (laws₂ : second.Laws m) (input : Tuple m.Value params) (idx : Index 2)
    {output : Tuple m.Value results} (ran : Exec m a.revert input (some output)) :
    ∃ mid, a.Observations m (g.denote m input a.demandWellFounded) idx mid output :=
  Proofs.observations_of_exec a (g.denote_solves m input a.demandWellFounded) laws₁ laws₂ idx ran

theorem Accepted.exec_of_runFuel (a : Accepted g first second)
    (fuel₁ fuel₂ : Nat) (input : Tuple m.Value params)
    {output : Tuple m.Value results} (ran : a.runFuel m fuel₁ fuel₂ input = some output) :
    Exec m a.revert input (some output) :=
  Proofs.exec_of_runFuel a fuel₁ fuel₂ ran

theorem Accepted.runFuel_of_observations (a : Accepted g first second)
    (laws₁ : first.Laws m) (laws₂ : second.Laws m) (total₁ : first.Total m) (total₂ : second.Total m)
    (input : Tuple m.Value params) (idx : Index 2)
    {mid : Tuple m.Value intermediate} {output : Tuple m.Value results}
    (observed : a.Observations m (g.denote m input a.demandWellFounded) idx mid output) :
    ∃ fuel₁ fuel₂, a.runFuel m fuel₁ fuel₂ input = some output :=
  Proofs.runFuel_of_observations a (g.denote_solves m input a.demandWellFounded)
    laws₁ laws₂ total₁ total₂ idx observed

/-- The converse constructs the first run before using the proved
handoff to construct the second. Slice totality is used in that direction. -/
theorem Accepted.exec_iff_observations (a : Accepted g first second)
    (laws₁ : first.Laws m) (laws₂ : second.Laws m) (total₁ : first.Total m) (total₂ : second.Total m)
    (input : Tuple m.Value params) (idx : Index 2) (output : Tuple m.Value results) :
    Exec m a.revert input (some output) ↔
      ∃ mid, a.Observations m (g.denote m input a.demandWellFounded) idx mid output :=
  ⟨a.observations_of_exec laws₁ laws₂ input idx, fun ⟨_, obs⟩ => by
    obtain ⟨k₁, k₂, ran⟩ := a.runFuel_of_observations laws₁ laws₂ total₁ total₂ input idx obs
    exact a.exec_of_runFuel k₁ k₂ input ran⟩

end Silmaril.SSA.PEG.Simple.Revert.While.Siblings
