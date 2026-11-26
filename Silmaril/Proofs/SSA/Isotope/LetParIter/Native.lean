module

public import Silmaril.SSA.Isotope.LetParIter.Defs

public section

namespace Silmaril.Isotope.LetParIter.Proofs

universe u v

theorem toLetIter?_embed {ν : Type u} {Φ : Type v} {n : Nat}
    (t : LetIter.LocallyNameless.Tm ν Φ n) : toLetIter? (embed t) = some t := by
  induction t <;> simp [embed, toLetIter?, *]

end Silmaril.Isotope.LetParIter.Proofs
