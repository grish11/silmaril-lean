module

public import Silmaril.SSA.Isotope.LetIter.Counterexample.Diagonal.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.CentralUnitDiagonal

/-! # Limits of central-unit Freyd models for context duplication -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

/-- A central unit comparison does not force transported value diagonals to be central
in a plain Freyd category. -/
theorem not_centralUnitTransportedDiagonals : ¬ CentralUnitTransportedDiagonals :=
  CentralUnitDiagonal.not_centralUnitTransportedDiagonals_proof

/-- Plain Freyd categories with a central unit can fail contextual bind associativity. -/
theorem not_centralUnitContextualBindAssoc : ¬ CentralUnitContextualBindAssoc :=
  CentralUnitDiagonal.not_centralUnitContextualBindAssoc_proof

end Silmaril.Isotope.LetIter.Semantics.Categorical
