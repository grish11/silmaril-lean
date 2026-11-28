module

public import Silmaril.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Defs
import Silmaril.Proofs.SSA.Isotope.Bridge.Acyclic.Positional.Capture.Institution.Rewrite.Repair.Sequence.Model.Coherence

/-! # Validating the concrete trace model -/

public section

namespace Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence

/-- All structural denotation witnesses agree in the concrete Kleisli trace
model, including witnesses with different internal label typings. -/
theorem traceRegionCoherent :
    letI := traceInstructions
    LambdaSSA.Semantics.Categorical.RegionTypingCoherent (Φ := signature.Instr) traceJ traceTypes :=
  traceRegionCoherent_proof

/-- The separating trace algebra is a model of the existing validated room. -/
noncomputable def validatedTraceModel : (grammarRoom traceJ signature).Mod :=
  validatedTrace traceRegionCoherent

/-- Admission retains the existing trace algebra's exact satisfaction. -/
theorem validatedTraceModel_sat_iff (e : GrammarEquation signature) :
    (grammarRoom traceJ signature).Sat validatedTraceModel e ↔
      ((LetCase.inst (Ctx.nil : Ctx Empty Sorts)).obj signature).Sat traceAlgebra (grammarCase e) :=
  Iff.rfl

end Silmaril.Isotope.Institution.Acyclic.Captured.Rewrite.Sequence
