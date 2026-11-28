module

public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Cuts.Defs
public import Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Thms

public section

namespace Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Cuts

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params results : List (Ty Data)} {n l : Nat}
variable {g : Graph P params results n l} {roles : Roles P} {rank : DemandRank n l}
variable [DecidableEq Data] [∀ ins out, DecidableEq (P ins out)]

/-- The result is the existing discovery witness. Its checker equation,
opcode laws and finite-return theorems apply to the original graph. -/
theorem discover_checked {cuts : List (Boundary g)} {budget : Nat} {found : Found g roles rank}
    (_ran : discover g roles rank cuts budget = .ok found) :
    Schedule.check g found.plan found.inputs rank = some found.gate :=
  found.checked

end Silmaril.SSA.PEG.Simple.Revert.Schedule.Automatic.Cuts
