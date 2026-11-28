module

import Silmaril.Logic.ManyValuedCatalogue.Discrete.Thms

/-! Checked examples of Bochvar's internal connectives and Boolean observations. -/

namespace Silmaril.Logic.ManyValuedCatalogue.Bochvar

example : ofOptionBool none = unknown := rfl

example : (ofBool true).toOptionBool = some true := rfl

example : neg unknown = unknown := rfl

example : and ff unknown = unknown := rfl

example : or tt unknown = unknown := rfl

example : imp ff unknown = unknown := rfl

example : iff unknown unknown = unknown := rfl

example : iff ff ff = tt ∧ iff tt ff = ff := by decide

end Silmaril.Logic.ManyValuedCatalogue.Bochvar
