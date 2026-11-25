module

public import Silmaril.SSA.Isotope.LetIter.Counterexample.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.WriterCounterexample

/-! # A countermodel to arbitrary-model exact LetIter soundness -/

public section

namespace Silmaril.Isotope.LetIter.Semantics.Categorical

/-- The current strong Elgot Freyd interface admits a writer interpretation in
which returning the bound value changes the recorded permutation. -/
theorem closedLetEtaUnsound : ¬ ClosedLetEtaSound :=
  WriterCounterexample.closedLetEtaUnsound_proof

end Silmaril.Isotope.LetIter.Semantics.Categorical
