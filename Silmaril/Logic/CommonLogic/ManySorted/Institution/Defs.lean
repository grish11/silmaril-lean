module

public import Silmaril.Logic.CommonLogic.ManySorted.Expansion.Thms

/-! Operation-typed Common Logic over the entire category of many-sorted FOL signatures. -/
@[expose] public section
noncomputable section

namespace Silmaril.Logic.CommonLogic.ManySorted.Institution

open CategoryTheory Silmaril.Logic.Institution Silmaril.Logic.Institution.Examples
open Silmaril.Logic.CommonLogic

abbrev room := Expansion.typedRoom

/-- Reduct retains every arrow between typed models, including along sort-identifying maps. -/
def corridor {S T : FOL.Signature} (f : S ⟶ T) : room S ⟶ room T :=
  ⟨Core.Formula.map (signatureMap f), typedReduct f,
    fun M p => Core.Formula.holds_map (signatureMap f) M.obj Fin.elim0 Fin.elim0 p⟩

end Silmaril.Logic.CommonLogic.ManySorted.Institution
