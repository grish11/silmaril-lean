module

public import Silmaril.Logic.TypeTheory.CIC.Positivity.Defs
public import Silmaril.Logic.TypeTheory.CIC.Typing.Defs

@[expose] public section

/-! # Checked declarations for the CIC core typing layer

The invariant shapes, argument sorts, index instances, strict positivity,
projection caches and elimination restrictions follow MetaRocq's
`common/theories/EnvironmentTyping.v` at
`c8cd46054518193103c3bb33aa6e15c7f489e72c` (MIT). This layer checks declarations
against `CoreTyping`; it accepts no variance annotations. It supplies no
semantic soundness assumption and does not certify the future full CIC rules.
-/

namespace Silmaril.Logic.TypeTheory.CIC

/-- Check a declaration in its own local universe context over the preceding environment. -/
def GlobalContext.forDeclaration (env : GlobalEnv) : UniverseDeclaration → GlobalContext
  | .monomorphic constraints =>
      { environment := env, localConstraints := constraints }
  | .polymorphic count constraints =>
      { environment := env, localParameters := count, localConstraints := constraints }

/-- Universe extensions must be scoped and satisfiable; monomorphic constraints are entailed. -/
def UniverseDeclaration.WellFormed (env : GlobalEnv) (decl : UniverseDeclaration) : Prop :=
  let sig := GlobalContext.forDeclaration env decl
  (∀ c ∈ sig.localConstraints,
    sig.AllowsUniverse c.left ∧ sig.AllowsUniverse c.right) ∧
  (∃ ρ, sig.Satisfies ρ) ∧
  match decl with
  | .monomorphic constraints =>
      ∀ c ∈ constraints, (GlobalContext.mk env 0 []).Entails c
  | .polymorphic _ _ => True

/-- A constructor's result head refers to its own member across parameters and arguments. -/
def ConstructorBody.conclusion (block : MutualInductiveBody) (member : ℕ)
    (constructor : ConstructorBody) : Expr :=
  Expr.mkApps (.rel (block.bodies.length - (member + 1) +
      block.parameters.length + constructor.arguments.length))
    (block.parameters.extendedList constructor.arguments.length ++ constructor.indices)

/-- Sorts of the assumptions of a context; definitions are checked but consume no sort entry. -/
inductive CoreContextSorts (sig : GlobalContext) (Γ : Context) :
    Context → List (SortExpr LevelName) → Prop where
  | nil : CoreContextSorts sig Γ [] []
  | assumption {Δ sorts na A s} : CoreContextSorts sig Γ Δ sorts →
      CoreTyping sig (Δ ++ Γ) A (.sort s) → s.HasRelevance na.relevance →
      CoreContextSorts sig Γ ({ binder := na, type := A } :: Δ) (s :: sorts)
  | definition {Δ sorts na value A s} : CoreContextSorts sig Γ Δ sorts →
      CoreTyping sig (Δ ++ Γ) A (.sort s) → s.HasRelevance na.relevance →
      CoreTyping sig (Δ ++ Γ) value A →
      CoreContextSorts sig Γ ({ binder := na, type := A, value := some value } :: Δ) sorts

/-- Inclusion among the four allowed-elimination classifications. -/
def AllowedElimination.Subset (a b : AllowedElimination) : Prop :=
  ∀ (ρ : LevelName → ℕ) s, a.Allows ρ s → b.Allows ρ s

/-- Prop and SProp count as propositional constructor-argument sorts. -/
def SortExpr.isPropositional : SortExpr LevelName → Bool
  | .prop | .sprop => true
  | .type _ => false

/-- Empty Prop and singleton Prop with propositional arguments permit large elimination. -/
def propElimination : List (List (SortExpr LevelName)) → AllowedElimination
  | [] => .intoAny
  | [sorts] => if sorts.all SortExpr.isPropositional then .intoAny else .intoPropSProp
  | _ => .intoPropSProp

/-- Only the empty SProp inductive permits large elimination. -/
def spropElimination : List (List (SortExpr LevelName)) → AllowedElimination
  | [] => .intoAny
  | _ => .intoSProp

/-- Universe sizes and propositional elimination restrictions are independently checked. -/
def InductiveBody.ValidSorts (sig : GlobalContext) (body : InductiveBody)
    (constructorSorts : List (List (SortExpr LevelName))) : Prop :=
  match body.sort with
  | .prop => body.elimination.Subset (propElimination constructorSorts)
  | .sprop => body.elimination.Subset (spropElimination constructorSorts)
  | .type _ => ∀ sorts ∈ constructorSorts, ∀ s ∈ sorts,
      ∀ ρ, sig.Satisfies ρ → s.Cumul ρ body.sort

/-- Checked constructor shape, arity, typing, dependent indices and strict positivity. -/
structure CoreCheckedConstructor (sig : GlobalContext) (block : MutualInductiveBody)
    (member : ℕ) (body : InductiveBody) (constructor : ConstructorBody)
    (sorts : List (SortExpr LevelName)) : Prop where
  arity : constructor.arguments.assumptionCount = constructor.arity
  shape : constructor.type = block.parameters.abstractProducts
    (constructor.arguments.abstractProducts (constructor.conclusion block member))
  type_sorted : ∃ s, CoreTyping sig block.aritiesContext constructor.type (.sort s) ∧
    s.HasRelevance body.relevance
  argument_sorts : CoreContextSorts sig (block.parameters ++ block.aritiesContext)
    constructor.arguments sorts
  indices : CoreContextInstance sig
    (constructor.arguments ++ block.parameters ++ block.aritiesContext)
    constructor.indices (Context.lift constructor.arguments.length 0 body.indices).reverse
  positive : PositiveConstructor block member 0 constructor.type

/-- The previous record fields are replaced by projections of the current record object. -/
def projectionSubstitution (reference : InductiveRef) (parameterCount : ℕ) : ℕ → List Expr
  | 0 => []
  | index + 1 => .projection ⟨reference, parameterCount, index⟩ (.rel 0) ::
      projectionSubstitution reference parameterCount index

/-- Projection names, relevance and cached dependent types are checked against constructor fields. -/
def CoreCheckedProjection (name : String) (block : MutualInductiveBody) (member : ℕ)
    (constructor : ConstructorBody) (index : ℕ) (projection : ProjectionBody) : Prop :=
  ∃ decl,
    (Context.smash [] (constructor.arguments ++ block.parameters))[
      constructor.arguments.assumptionCount - (index + 1)]? = some decl ∧
    decl.binder.name = some projection.name ∧
    projection.relevance = decl.binder.relevance ∧
    projection.type =
      ((decl.type.lift 1 index).subst
        (projectionSubstitution ⟨name, member⟩ block.parameterCount index) 0).subst
          (inductiveSubstitution name block.universes.abstractInstance block.bodies)
          (block.parameterCount + 1)

/-- Primitive records have one constructor, no indices, unrestricted elimination and all projections. -/
def CoreCheckedProjections (name : String) (block : MutualInductiveBody) (member : ℕ)
    (body : InductiveBody) : Prop :=
  body.projections = [] ∨ ∃ constructor,
    body.constructors = [constructor] ∧ body.indices = [] ∧ body.elimination = .intoAny ∧
    body.projections.length = constructor.arguments.assumptionCount ∧
    ∀ index projection, body.projections[index]? = some projection →
      CoreCheckedProjection name block member constructor index projection

/-- Checked arity, constructors, projections and sort policies of a single member. -/
structure CoreCheckedInductive (sig : GlobalContext) (name : String)
    (block : MutualInductiveBody) (member : ℕ) (body : InductiveBody) : Prop where
  shape : body.type = block.parameters.abstractProducts
    (body.indices.abstractProducts (.sort body.sort))
  arity_sorted : ∃ s, CoreTyping sig [] body.type (.sort s) ∧ s.HasRelevance .relevant
  constructors : ∃ (constructorSorts : List (List (SortExpr LevelName))), constructorSorts.length = body.constructors.length ∧
    (∀ (index : ℕ) (constructor : ConstructorBody) (sorts : List (SortExpr LevelName)),
      body.constructors[index]? = some constructor → constructorSorts[index]? = some sorts →
      CoreCheckedConstructor sig block member body constructor sorts) ∧
    body.ValidSorts sig constructorSorts
  projections : CoreCheckedProjections name block member body
  relevance : body.sort.HasRelevance body.relevance

/-- Checked mutual declaration for the core layer; variance remains deliberately unavailable. -/
structure CoreCheckedBlock (sig : GlobalContext) (name : String)
    (block : MutualInductiveBody) : Prop where
  members : ∀ member body, block.bodies[member]? = some body →
    CoreCheckedInductive sig name block member body
  parameters : CoreWfLocal sig block.parameters
  parameter_count : block.parameters.assumptionCount = block.parameterCount
  no_variance : block.variance = none

/-- Checked constant types and bodies. Bodyless declarations are language-level assumptions. -/
def CoreCheckedConstant (sig : GlobalContext) (constant : ConstantBody) : Prop :=
  (∃ s, CoreTyping sig [] constant.type (.sort s) ∧ s.HasRelevance constant.relevance) ∧
  ∀ value, constant.body = some value → CoreTyping sig [] value constant.type

/-- A declaration is checked over its preceding environment, never over its own constant name. -/
def CoreCheckedDeclaration (env : GlobalEnv) (name : String) : GlobalDeclaration → Prop
  | .constant constant => constant.universes.WellFormed env ∧
      CoreCheckedConstant (GlobalContext.forDeclaration env constant.universes) constant
  | .inductiveBlock block => block.universes.WellFormed env ∧
      CoreCheckedBlock (GlobalContext.forDeclaration env block.universes) name block

/-- Declarations are checked in order and global names cannot be repeated. -/
inductive CoreCheckedDeclarations (levels : List String) (constraints : List UniverseConstraint) :
    List (String × GlobalDeclaration) → Prop where
  | nil : CoreCheckedDeclarations levels constraints []
  | cons {declarations name declaration} : CoreCheckedDeclarations levels constraints declarations →
      name ∉ declarations.map Prod.fst →
      CoreCheckedDeclaration ⟨levels, constraints, declarations⟩ name declaration →
      CoreCheckedDeclarations levels constraints ((name, declaration) :: declarations)

/-- Global universe constraints are scoped and satisfiable, in addition to declaration checks. -/
def CoreCheckedEnvironment (env : GlobalEnv) : Prop :=
  env.globalLevels.Nodup ∧
  (∀ c ∈ env.constraints,
    (GlobalContext.mk env 0 []).AllowsUniverse c.left ∧ (GlobalContext.mk env 0 []).AllowsUniverse c.right) ∧
  (∃ ρ, (GlobalContext.mk env 0 []).Satisfies ρ) ∧
  CoreCheckedDeclarations env.globalLevels env.constraints env.declarations

namespace DeclarationExamples

/-- Nullary constructor of a single-member natural-number block. -/
def naturalZero : ConstructorBody :=
  { name := "O", arguments := [], indices := [], type := .rel 0, arity := 0 }

/-- Unary strictly positive recursive constructor in the same block. -/
def naturalSuccessor : ConstructorBody :=
  { name := "S", arguments := [{ binder := {}, type := .rel 0 }], indices := [],
    type := .prod {} (.rel 0) (.rel 1), arity := 1 }

def naturalBody : InductiveBody :=
  { name := "nat", indices := [], sort := .type .zero, type := .sort (.type .zero),
    elimination := .intoAny, constructors := [naturalZero, naturalSuccessor],
    projections := [], relevance := .relevant }

def naturalBlock : MutualInductiveBody :=
  { recursivity := .finite, parameterCount := 0, parameters := [], bodies := [naturalBody],
    universes := .monomorphic [] }

def naturalEnvironment : GlobalEnv :=
  { declarations := [("nat", .inductiveBlock naturalBlock)] }

end DeclarationExamples

end Silmaril.Logic.TypeTheory.CIC
