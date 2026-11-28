module

public import Silmaril.SSA.RVSDG.NestedTheta.Petri.Cut.Defs

/-! The continuation marking on the far side of an existing cut. -/

@[expose] public section

namespace Silmaril.SSA.RVSDG.NestedTheta.Petri

universe u v w

variable {V S : Type u} {Op : Dialect.{u, v} V S}
variable {args bank outs : Ports (PortType V S)}

def Cut.rest (m : Model.{u, v, w} Op) :
    {past frontSigs wholeSigs tailSigs : List (Ports (PortType V S))} →
    {front : Term Op args past frontSigs bank} → {whole : Term Op args past wholeSigs outs} →
    {tail : Term Op args (extend past frontSigs) tailSigs outs} →
    Cut front whole tail → Marking m whole → Marking m tail
  | _, _, _, _, _, _, _, .stop .., mark => mark
  | _, _, _, _, _, _, _, .bind _ _ cut, mark => cut.rest m mark.2

end Silmaril.SSA.RVSDG.NestedTheta.Petri
