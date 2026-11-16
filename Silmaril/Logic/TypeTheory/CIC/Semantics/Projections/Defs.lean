module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Operational.Thms

@[expose] public section

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

universe u

/-- A runtime regression reference with one parameter and two fields. -/
def projectionRegressionReference : InductiveRef := ⟨"projection_runtime", 0⟩

/-- A genuine curried constructor trace; no checked source declaration is asserted here. -/
noncomputable def projectionRegressionGlobals (P A B : Value.{u}) : GlobalValues.{u} :=
  { constant := fun _ _ => none
    inductiveType := fun _ _ => none
    constructor := fun reference index ui =>
      if reference = projectionRegressionReference ∧ index = 0 ∧ ui = [] then
        some (traceLambda P (fun p => traceLambda A (fun a => traceLambda B
          (fun b => constructorValue 0 [p, a, b]))))
      else none }

/-- Actual source constructor application, with local arguments in source order. -/
def projectionRegressionConstructor : Expr :=
  Expr.mkApps (.constructor projectionRegressionReference 0 []) [.rel 2, .rel 1, .rel 0]

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
