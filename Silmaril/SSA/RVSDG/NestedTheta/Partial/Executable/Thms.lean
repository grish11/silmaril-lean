module

public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable.Defs
public import Silmaril.SSA.RVSDG.NestedTheta.Partial.Thms
import Silmaril.Proofs.SSA.RVSDG.NestedTheta.Partial.Executable.Adequacy

public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable

universe u v w
variable {V S : Type u} {Op : Dialect.{u,v} V S} {m : Model.{u,v,w} Op}
variable {args outs : Ports (PortType V S)} {sigs : List (Ports (PortType V S))}

/-- A successful execution at some bound is equivalent to a finite
derivation of the full typed output. -/
theorem returns_iff (actions : Actions m) (g : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    (∃ fuel, run actions g fuel input = some output) ↔ Partial.returns m g input output :=
  Proofs.returns_iff actions g input output

theorem run_iff_observe (actions : Actions m) (g : Graph Op args [] sigs outs)
    (input : Tuple m.Val args) (output : Tuple m.Val outs) :
    (∃ fuel, run actions g fuel input = some output) ↔ Partial.observe m g input = Part.some output :=
  (returns_iff actions g input output).trans (Partial.observe_eq_some m g input output).symm

end Silmaril.SSA.RVSDG.NestedTheta.Partial.Executable
