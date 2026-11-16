module

public import Silmaril.Logic.TypeTheory.CIC.Semantics.Constructors.Definitions.Defs
public import Silmaril.Proofs.Logic.TypeTheory.CIC.DefinedTelescopes

@[expose] public section

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

export Silmaril.Proofs.Logic.TypeTheory.CIC.DefinedTelescopeLaws
  (interpretsTelescope_subst SourceTelescopeData.interpretsSmash SourceTelescopeData.arguments_length
    SourceTelescopeData.sourceValues_length SourceTelescopeData.interpretsLocal
    SourceTelescopeData.evaluatesProducts SourceTelescopeData.evaluatesLambdas
    assumptionCount_append assumptionCount_reverse)

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
