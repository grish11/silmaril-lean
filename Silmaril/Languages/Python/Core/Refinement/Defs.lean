module

public import Silmaril.Languages.Python.Core.Defs
public import Silmaril.Semantics.Operational.Maximal.Defs

/-!
# Python Core behavior comparison

The common program is a closed `Body`. A profile always enters at
`Body.start` for purposes of comparison. The existing state policy checks
the whole initial expression and marks an unsupported start as UB. This
gives coarse whole-program completion, including when unsupported syntax
lies in an operand that left-to-right evaluation would never reach.
-/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Refinement

open Semantics.Operational

/-- The visible exit label and the terminal payload both carry a return or
an uncaught exception. The common view keeps every maximal observation. -/
abbrev Observation := RunObservation Completion Completion

def expected (body : Body) : Observation :=
  .finite [body.value.eval] (.terminal (.returned body.value.eval))

/-- A larger feature profile enables at least the operations of the smaller one. -/
def FeatureLE (smaller larger : Profile) : Prop :=
  ∀ op, smaller.allows op → larger.allows op

def runSem (profile : Profile) : RunSem State Completion Completion where
  toLabelled := labelled profile
  blocked _ := False
  ub := (semantics profile).ub

/-- Every closed body has an entry at its own start. The executable Core
profile continues to use its separate admission relation. -/
def comparison (profile : Profile) : HasRuns Body State Completion Completion where
  initial body state := state = body.start
  semantics := runSem profile

def behaviors (profile : Profile) : RunBehaviors Body Observation :=
  (comparison profile).completed id

end Silmaril.Languages.Python.Core.Refinement
