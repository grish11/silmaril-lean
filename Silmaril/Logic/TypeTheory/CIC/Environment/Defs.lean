module

public import Silmaril.Logic.TypeTheory.CIC.Instantiation.Defs

@[expose] public section

/-! # Raw CIC declaration environments

Adapted from `common/theories/Environment.v` in MetaRocq at
`c8cd46054518193103c3bb33aa6e15c7f489e72c` (MIT; retained notice in
`licenses/MetaRocq-MIT.txt`). These records do not certify typing, positivity,
guardedness or consistency. Machine-primitive retroknowledge is excluded.
-/

namespace Silmaril.Logic.TypeTheory.CIC

universe u

/-- Global universe names and local universe parameters are distinct. -/
inductive LevelName where
  | global (name : String)
  | parameter (index : ℕ)
  deriving DecidableEq, Repr

abbrev Expr := Term LevelName
abbrev Universe := UniverseExpr LevelName
abbrev Context := List (ContextDecl Expr)

/-- Relations allowed in a universe constraint. -/
inductive UniverseRelation where
  | equal
  | lessOrEqual
  | less
  deriving DecidableEq, Repr

structure UniverseConstraint where
  left : Universe
  relation : UniverseRelation
  right : Universe
  deriving DecidableEq, Repr

/-- A numerical valuation satisfies one universe constraint. -/
def UniverseConstraint.Holds (ρ : LevelName → ℕ) (c : UniverseConstraint) : Prop :=
  match c.relation with
  | .equal => c.left.eval ρ = c.right.eval ρ
  | .lessOrEqual => c.left.eval ρ ≤ c.right.eval ρ
  | .less => c.left.eval ρ < c.right.eval ρ

/-- Universe declarations distinguish fixed global constraints from local polymorphism. -/
inductive UniverseDeclaration where
  | monomorphic (constraints : List UniverseConstraint)
  | polymorphic (parameterCount : ℕ) (constraints : List UniverseConstraint)
  deriving DecidableEq, Repr

/-- Only Set and named levels are Rocq universe-instance arguments. -/
def UniverseExpr.IsAtomic {Level : Type u} : UniverseExpr Level → Prop
  | .zero | .level _ => True
  | .succ _ | .max _ _ => False

/-- Out-of-range local parameters map to Set, as in PCUIC's total raw operation.

Typing must separately require the declared instance length and scope.
-/
def instanceSubstitution (universeInstance : List Universe) : LevelName → Universe
  | .global g => .level (.global g)
  | .parameter i => universeInstance[i]?.getD .zero

/-- Instantiate local universe parameters; cached declaration contexts remain unchanged. -/
def Expr.instantiate (universeInstance : List Universe) (t : Expr) : Expr :=
  t.substUniverses (instanceSubstitution universeInstance)

/-- Parameter and index contexts are newest-first, including local definitions. -/
structure ConstructorBody where
  name : String
  arguments : Context
  indices : List Expr
  type : Expr
  arity : ℕ
  deriving Repr

structure ProjectionBody where
  name : String
  relevance : Relevance
  type : Expr
  deriving Repr

structure InductiveBody where
  name : String
  indices : Context
  sort : SortExpr LevelName
  type : Expr
  elimination : AllowedElimination
  constructors : List ConstructorBody
  projections : List ProjectionBody
  relevance : Relevance
  deriving Repr

inductive RecursivityKind where
  | finite
  | cofinite
  | nonrecursive
  deriving DecidableEq, Repr

inductive Variance where
  | irrelevant
  | covariant
  | invariant
  deriving DecidableEq, Repr

structure MutualInductiveBody where
  recursivity : RecursivityKind
  parameterCount : ℕ
  parameters : Context
  bodies : List InductiveBody
  universes : UniverseDeclaration
  variance : Option (List Variance) := none
  deriving Repr

structure ConstantBody where
  type : Expr
  body : Option Expr
  universes : UniverseDeclaration
  relevance : Relevance
  deriving Repr

inductive GlobalDeclaration where
  | constant (body : ConstantBody)
  | inductiveBlock (body : MutualInductiveBody)
  deriving Repr

/-- Newest-first declarations. Checked environments must also exclude duplicate names. -/
structure GlobalEnv where
  globalLevels : List String := []
  constraints : List UniverseConstraint := []
  declarations : List (String × GlobalDeclaration) := []
  deriving Repr

/-- Raw lookup chooses the most recent declaration of a name. -/
def GlobalEnv.lookup (env : GlobalEnv) (name : String) : Option GlobalDeclaration :=
  (env.declarations.find? (fun d => d.1 == name)).map Prod.snd

def GlobalEnv.lookupConstant (env : GlobalEnv) (name : String) : Option ConstantBody := do
  let .constant body ← env.lookup name | none
  some body

def GlobalEnv.lookupInductive (env : GlobalEnv) (ref : InductiveRef) :
    Option (MutualInductiveBody × InductiveBody) := do
  let .inductiveBlock block ← env.lookup ref.block | none
  let body ← block.bodies[ref.index]?
  some (block, body)

def GlobalEnv.lookupConstructor (env : GlobalEnv) (ref : InductiveRef) (index : ℕ) :
    Option (MutualInductiveBody × InductiveBody × ConstructorBody) := do
  let (block, body) ← env.lookupInductive ref
  let constructor ← body.constructors[index]?
  some (block, body, constructor)

def GlobalEnv.lookupProjection (env : GlobalEnv) (ref : ProjectionRef) :
    Option (MutualInductiveBody × InductiveBody × ConstructorBody × ProjectionBody) := do
  let (block, body, constructor) ← env.lookupConstructor ref.inductiveRef 0
  let projection ← body.projections[ref.argument]?
  some (block, body, constructor, projection)

end Silmaril.Logic.TypeTheory.CIC
