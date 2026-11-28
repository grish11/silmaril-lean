module

public import Silmaril.SSA.PEG.Simple.Revert.While.Region.Defs
import Silmaril.Proofs.SSA.PEG.Simple.Revert.While.Region.Total

public section

namespace Silmaril.SSA.PEG.Simple.Revert.While.Region

open RVSDG (Tuple)

universe u v w

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params vars outs : List (Ty Data)} {result : Ty Data} {n l : Nat}
variable {g : Graph P params [result] n l} {m : Interpretation.{u,v,w} P}

/-- Total primitives give defined execution of a primitive-only schedule
on any defined store, regardless of the graph's loop-key space. -/
theorem Schedule.lower_total {roots : Tuple (Ref g.sort) outs} {scope : Tuple (Ref g.sort) vars}
    (code : Schedule g false roots scope)
    (total : ∀ {ins out} (op : P ins out) args, ∃ val, m.run op args = some val)
    (store : Tuple m.Value vars) : ∃ out, code.lower.runLoopFree m store = some out :=
  TotalProofs.primitive_schedule_total code total store

end Silmaril.SSA.PEG.Simple.Revert.While.Region
