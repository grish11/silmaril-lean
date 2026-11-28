module

public import Silmaril.SSA.PEG.Figure19.Defs
public import Silmaril.SSA.PEG.Simple.Structured.Defs

/-! # Checking Figure 19 on a structured SIMPLE compilation -/

@[expose] public section

namespace Silmaril.SSA.PEG.Figure19.Structured

open PEG.Simple.Structured (translate program rank)

universe u v

variable {Data : Type u} {P : InstructionSet.{u,v} Data}
variable {params : List (Ty Data)} {t : Ty Data}

/-- Check the inward convention on the actual compiler graph, using
the compiler's finite rank for the independent Figure 11 gate. -/
def check (p : Simple.Program P true params t) (neg : P [.bool] .bool) (fuel : Nat) :
    Option (Guarded (translate p neg) .inward) :=
  checkGuarded (translate p neg) .inward fuel (rank (program p neg).nodes.length)

end Silmaril.SSA.PEG.Figure19.Structured
