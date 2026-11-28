module

public import Silmaril.SSA.Isotope.Bridge.NamedFlat.Typing.Expected.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.NamedFlat.Typing.Expected

public section

namespace Silmaril.Isotope.Bridge.NamedFlat

universe u v
variable {Base : Type u} {F : Type v} [DecidableEq Base] [HasTy F (Ty Base)]

theorem checkExpected_sound {blocks exits n : Nat} (graph : LambdaSSA.FiniteCFG F blocks exits n)
    (captures : BoundCtx (Ty Base) n) (internal : Fin blocks → Ty Base)
    (external : Fin exits → Ty Base) (accepted : checkExpected graph captures internal external = true) :
    graph.HasType captures internal external :=
  Proofs.SSA.Isotope.Bridge.NamedFlat.checkExpected_sound graph captures internal external accepted

end Silmaril.Isotope.Bridge.NamedFlat
