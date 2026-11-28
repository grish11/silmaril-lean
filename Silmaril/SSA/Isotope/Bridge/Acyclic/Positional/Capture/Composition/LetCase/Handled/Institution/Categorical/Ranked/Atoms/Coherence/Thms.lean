module

public import Silmaril.SSA.Isotope.LetSeq.StraightLine.Structural.Categorical.Defs
public import Silmaril.SSA.Isotope.LambdaSSA.Categorical.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Composition.LetCase.Handled.Institution.AtomCoherence

/-! # Region coherence of the ordered trace interpretation with atoms

The existing ordered trace interpretation gives every atom the carrier
`Nat`. The existing proof that its native region witnesses are coherent is
stated for the atom-free types. The same erasure argument applies at any
atom carriers, so the interpretation with atoms can be a model of the
existing rooms.
-/

public section

namespace Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution

open LambdaSSA.Semantics.Categorical (RegionTypingCoherent)
open LetSeq.StraightLine.Structural.Categorical (traceJ traceTypes traceInstructions)
open scoped LetSeq.StraightLine.Structural

/-- The ordered trace interpretation whose atoms are natural numbers has
coherent native region witnesses at every exact input and exit interface. -/
theorem atomTrace_region_coherent {α Φ : Type} [HasTy Φ (Ty α)] :
    letI := traceInstructions (α := α) (Φ := Φ)
    RegionTypingCoherent (Φ := Φ) (traceJ (α := α) (Φ := Φ)) (traceTypes α) :=
  atomTrace_region_coherent_proof

end Silmaril.Isotope.LambdaSSA.Acyclic.Positional.Capture.Composition.Handled.Institution
