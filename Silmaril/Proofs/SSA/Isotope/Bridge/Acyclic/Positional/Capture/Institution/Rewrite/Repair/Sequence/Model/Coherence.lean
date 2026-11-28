module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Defs
import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Kleisli.Thms

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

open LambdaSSA.Semantics.Categorical (RegionTypingCoherent)

theorem traceRegionCoherent_proof :
    letI := traceInstructions
    RegionTypingCoherent (Φ := signature.Instr) traceJ traceTypes := by
  apply Kleisli.regionCoherent model _ (ExceptT.mk (WriterT.mk Part.none))
  intro f hf
  cases f <;> cases hf

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence
