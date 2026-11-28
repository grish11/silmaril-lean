module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.Thms

/-! # Objects of the native captured LetCase category -/

@[expose] public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Case

/-- Nonempty ordered interfaces for the native LetCase equation classes, at
the same primitive signature and structural older context as the written
interfaces. Each interface is read at its literal packed type. -/
structure Interface (Φ : Type) {d : Nat} (β : LetCase.Structural.Finite.Context d)
    (input : LetCase.Structural.Finite.StructuralContext β) where
  exits : LCtx (Ty Empty)
  nonempty : exits ≠ []

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Case
