module

public import Silmaril.Logic.TypeTheory.CIC.Declarations.Lookup.Thms
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Constructors.Thms
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Projections.Thms
public import Silmaril.Logic.TypeTheory.CIC.Semantics.Instantiation.Thms
public import Silmaril.Proofs.Logic.TypeTheory.CIC.ProjectionCaches

@[expose] public section

/-! # Generic dependent primitive-projection cache realization

Definition-free source fields and parameters use their genuine constructor
telescope interpretation in the actual declaration-instance world. Earlier
field projections and the actual mutual references evaluate the checked
cache; universe instantiation and the actual scrutinee/parameter substitution
then give its exact source type. Constructor-layer inversion recovers field
membership. No projection-result interpretation or global fundamental theorem
is assumed. Parameter-count agreement remains explicit.
-/

namespace Silmaril.Logic.TypeTheory.CIC.SetSemantics

export Silmaril.Proofs.Logic.TypeTheory.CIC.ProjectionCacheLaws
  (smash_no_definitions telescope_field projectionSubstitution_evaluates projection_cache_at_record projection_cache_evaluates projection_point
    constructorLayer_projection_rule checked_projection_source_and_value)

end Silmaril.Logic.TypeTheory.CIC.SetSemantics
