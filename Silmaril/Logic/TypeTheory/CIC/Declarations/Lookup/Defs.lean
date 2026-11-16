module

public import Silmaril.Logic.TypeTheory.CIC.Declarations.Thms

@[expose] public section

/-! # Checked declarations recovered from actual global lookup

The preceding declaration list is the exact suffix used by ordered checking.
Its original universe names and constraints are retained. The witnesses carry
the actual constructor-sort lists and dependent projection caches; they do
not interpret those declarations or assume a fundamental theorem.
-/

namespace Silmaril.Logic.TypeTheory.CIC

/-- A global declaration was checked over its exact preceding environment. -/
structure CheckedDeclarationLookup (env : GlobalEnv) (name : String)
    (declaration : GlobalDeclaration) (previous : List (String × GlobalDeclaration)) : Prop where
  order : ∃ newer, env.declarations = newer ++ (name, declaration) :: previous
  environment : CoreCheckedEnvironment { env with declarations := previous }
  checked : CoreCheckedDeclaration { env with declarations := previous } name declaration

/-- An actual member lookup retains its checked block and universe declaration. -/
structure CheckedInductiveLookup (env : GlobalEnv) (reference : InductiveRef)
    (block : MutualInductiveBody) (body : InductiveBody)
    (previous : List (String × GlobalDeclaration)) : Prop where
  declaration : CheckedDeclarationLookup env reference.block (.inductiveBlock block) previous
  member : block.bodies[reference.index]? = some body
  universes : block.universes.WellFormed { env with declarations := previous }
  checked : CoreCheckedBlock
    (GlobalContext.forDeclaration { env with declarations := previous } block.universes) reference.block block

/-- Constructor lookup recovers genuine typing, positivity and the original sort witnesses. -/
structure CheckedConstructorLookup (env : GlobalEnv) (reference : InductiveRef) (index : ℕ)
    (block : MutualInductiveBody) (body : InductiveBody) (constructor : ConstructorBody)
    (previous : List (String × GlobalDeclaration)) : Prop where
  block_checked : CheckedInductiveLookup env reference block body previous
  constructor_lookup : body.constructors[index]? = some constructor
  sorts : ∃ allSorts sorts,
    allSorts.length = body.constructors.length ∧ allSorts[index]? = some sorts ∧
    body.ValidSorts
      (GlobalContext.forDeclaration { env with declarations := previous } block.universes) allSorts ∧
    CoreCheckedConstructor
      (GlobalContext.forDeclaration { env with declarations := previous } block.universes)
      block reference.index body constructor sorts

/-- Actual primitive projection lookup recovers the complete checked record metadata.
The reference's parameter-count field is checked separately by source typing. -/
structure CheckedProjectionLookup (env : GlobalEnv) (reference : ProjectionRef)
    (block : MutualInductiveBody) (body : InductiveBody) (constructor : ConstructorBody)
    (projection : ProjectionBody) (previous : List (String × GlobalDeclaration)) : Prop where
  constructor_checked : CheckedConstructorLookup env reference.inductiveRef 0 block body constructor previous
  projection_lookup : body.projections[reference.argument]? = some projection
  singleton : body.constructors = [constructor]
  no_indices : body.indices = []
  elimination : body.elimination = .intoAny
  field_count : body.projections.length = constructor.arguments.assumptionCount
  argument_bound : reference.argument < constructor.arguments.assumptionCount
  checked : CoreCheckedProjection reference.inductiveRef.block block reference.inductiveRef.index
    constructor reference.argument projection

end Silmaril.Logic.TypeTheory.CIC
