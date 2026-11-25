module

public import Silmaril.Languages.Python.Core.Refinement.Defs

/-!
# First unsupported operation in Python Core

This comparison follows the existing Core steps. It guards the primitive
selected by left-to-right evaluation and uses the same coarse completion
when a run reaches an unsupported operation.
-/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Refinement.Dynamic

open Semantics.Operational

/-- The operation selected for the next expression reduction. -/
inductive Focus : Expr → BinOp → Prop where
  | compute {op left right} : Focus (.binary op (.int left) (.int right)) op
  | left {op left right active} : Focus left active → Focus (.binary op left right) active
  | right {op left right active} : Focus right active → Focus (.binary op (.int left) right) active

/-- Literals and exits require no arithmetic operation. In a returning
expression, only the selected operation needs to be supported. -/
def Allows (profile : Profile) : State → Prop
  | .returning expr => ∀ op, Focus expr op → profile.allows op
  | .raising _ | .finished _ => True

def policy (profile : Profile) : WithUB State Completion :=
  (WithUB.ofOpSem ordinary).enforce (Allows profile)

def runSem (profile : Profile) : RunSem State Completion Completion where
  step source label target := Allows profile source ∧ Step source label target
  observe := (policy profile).observe
  blocked _ := False
  ub := (policy profile).ub

def comparison (profile : Profile) : HasRuns Body State Completion Completion where
  initial body state := state = body.start
  semantics := runSem profile

def behaviors (profile : Profile) : RunBehaviors Body Observation :=
  (comparison profile).completed id

end Silmaril.Languages.Python.Core.Refinement.Dynamic
