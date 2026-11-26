module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed.Defs
public import Silmaril.SSA.PEG.Simple.While.Thms
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Closed

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params carried results : List (Ty Data)} {n : Nat}
variable {g : Graph P params results n 1} {m : Interpretation.{u,v,w} P}

theorem Accepted.demandWellFounded (a : Accepted g carried) : WellFounded g.Demand :=
  g.demandWellFounded_of_check a.rank a.ranked

/-- Every finite successful emitted run gives the original ordered
observation. The trace identifies one least pass count, and every eval
uses the same exit and the defined prefix of its carried slot. -/
theorem Accepted.observe_of_exec (a : Accepted g carried) (laws : a.Laws m) (input : Tuple m.Value params) (idx : Index 1)
    {output : Tuple m.Value results} (ran : Exec m a.revert input (some output)) :
    g.observe m (g.denote m input a.demandWellFounded) idx = output.map (fun _ => some) :=
  Proofs.observe_of_exec a laws (g.denote_solves m input a.demandWellFounded) idx ran

theorem Accepted.exec_of_runFuel (a : Accepted g carried) (fuel : Nat) (input : Tuple m.Value params)
    {output : Tuple m.Value results} (ran : a.runFuel m fuel input = some output) :
    Exec m a.revert input (some output) :=
  Proofs.exec_of_runFuel a fuel ran

end Silmaril.SSA.PEG.Simple.Revert.While.Region.Closed
