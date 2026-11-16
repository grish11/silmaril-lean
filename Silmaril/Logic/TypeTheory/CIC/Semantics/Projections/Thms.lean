module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Projections.Defs
public import Silmaril.Proofs.Logic.TypeTheory.CIC.PrimitiveProjections

@[expose] public section

/-! # Primitive projection computation in the canonical evaluation kernel

Primitive records use constructor zero and the actual source parameter offset.
Determinism, local and universe substitution/reflection, bounded universe
agreement, carrier lifting and operational compatibility cover this rule.
Tagged values do not encode inductive references: checked metadata and field
typing remain separate obligations, with no global soundness premise here.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

export Silmaril.Proofs.Logic.TypeTheory.CIC.PrimitiveProjectionLaws
  (evaluates_projection_iff evaluates_projection_wrong_tag projection_step_values
    projectionRegression_constructor_evaluates projectionRegression_values evaluates_nested_projections)

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
