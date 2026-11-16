module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Coherence.Thms
public import Silmaril.Proofs.Logic.TypeTheory.CIC.LocalSemantics

@[expose] public section

/-! # Concrete local declarations, lets and delta reduction

Interpreted local declarations realize the actual CIC variable rule, including
the full de Bruijn lift of a declaration's type. Local definitions and
interpreted constant bodies give same-value endpoints of actual delta steps.
The let rule uses an interpreted local definition and the actual let-shaped
syntactic type. No interpretation or inhabitant is inferred merely from a
checked declaration; global assignments remain explicit.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

export Silmaril.Proofs.Logic.TypeTheory.CIC.LocalSemanticsLaws
  (local_lookup local_rule local_delta_step_values evaluates_append constant_local_rule let_rule global_delta_step_values)

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
