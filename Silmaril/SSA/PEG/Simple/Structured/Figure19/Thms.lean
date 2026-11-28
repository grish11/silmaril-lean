module

public import Silmaril.SSA.PEG.Figure19.Defs
public import Silmaril.SSA.PEG.Simple.Structured.Defs
import Silmaril.Proofs.SSA.PEG.Simple.Structured.Figure19

public section

namespace Silmaril.SSA.PEG.Simple.Structured

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {t : Ty Data}

/-- Every structured SIMPLE compilation has an inward Figure 19
derivation at the exact depths computed by the checker. -/
theorem translate_figure19 (p : Program P true params t) (neg : P [.bool] .bool) :
    let g := translate p neg
    let depth := PEG.Figure19.inferDepth g.forest (program p neg).nodes.length
    PEG.Figure19.FitsForest g.forest depth ∧ PEG.Figure19.CFGContext g depth .inward :=
  Proofs.Figure19.programTyped p neg

end Silmaril.SSA.PEG.Simple.Structured
