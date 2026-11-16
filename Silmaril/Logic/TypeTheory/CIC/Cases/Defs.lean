module

public import Silmaril.Logic.TypeTheory.CIC.Context.Defs

@[expose] public section

/-! # CIC dependent-case contexts and branch types

Adapted from MetaRocq `pcuic/theories/Syntax/PCUICCases.v` at
`c8cd46054518193103c3bb33aa6e15c7f489e72c` (MIT). Parameters and constructor
lets are expanded before instantiating motive and branch contexts.
-/

namespace Silmaril.Logic.TypeTheory.CIC

/-- Ignore printable names, preserving relevance and all declaration types and values. -/
def Context.withoutNames (Γ : Context) : Context :=
  Γ.map fun d => { d with binder := { d.binder with name := none } }

/-- Retain the user's binder names on a canonically computed declaration context. -/
def Context.useNames (cached canonical : Context) : Context :=
  List.zipWith (fun c d => { d with binder := { d.binder with name := c.binder.name } })
    cached canonical

/-- The raw declaration cache for a case motive includes its indices and scrutinee. -/
def predicateDeclarationContext (reference : InductiveRef) (block : MutualInductiveBody)
    (body : InductiveBody) : Context :=
  let indices := Context.expandLetsContext block.parameters 0 body.indices
  let indType := Expr.mkApps (.inductiveType reference block.universes.abstractInstance)
    (Context.extendedList (indices ++ Context.smash [] block.parameters) 0)
  { binder := { name := some body.name, relevance := body.relevance }, type := indType } :: indices

/-- Instantiate the canonical motive context and retain only the cache's printable names. -/
def casePredicateContext (reference : InductiveRef) (block : MutualInductiveBody)
    (body : InductiveBody) (p : Predicate Expr LevelName) : Context :=
  Context.useNames p.context
    (Context.instantiateCase p (predicateDeclarationContext reference block body))

/-- Constructor branch cache, with mutual names substituted and parameter lets expanded. -/
def branchDeclarationContext (reference : InductiveRef) (block : MutualInductiveBody)
    (constructor : ConstructorBody) : Context :=
  Context.expandLetsContext block.parameters 0
    (Context.subst (inductiveSubstitution reference.block block.universes.abstractInstance
      block.bodies) block.parameters.length constructor.arguments)

/-- Canonical instantiated branch context with user-visible names. -/
def caseBranchContext (reference : InductiveRef) (block : MutualInductiveBody)
    (constructor : ConstructorBody) (p : Predicate Expr LevelName) (branch : Branch Expr) : Context :=
  Context.useNames branch.context
    (Context.instantiateCase p (branchDeclarationContext reference block constructor))

/-- A branch returns the motive applied to the constructor's actual indices and value. -/
def caseBranchType (reference : InductiveRef) (block : MutualInductiveBody)
    (constructor : ConstructorBody) (p : Predicate Expr LevelName)
    (motive : Expr) (index : ℕ) : Expr :=
  let count := constructor.arguments.length
  let constructorTerm := Expr.mkApps (.constructor reference index p.universeInstance)
    (p.parameters.map (Term.lift count 0) ++ Context.extendedList constructor.arguments 0)
  let parameters := Context.instantiate p.universeInstance block.parameters
  let indices := constructor.indices.map fun t =>
    let instantiated := (Expr.instantiate p.universeInstance t).subst
      (inductiveSubstitution reference.block p.universeInstance block.bodies)
      (block.parameters.length + count)
    (Context.expandLetsAt parameters count instantiated).subst p.parameters.reverse count
  Expr.mkApps (motive.lift count 0) (indices ++ [constructorTerm])

end Silmaril.Logic.TypeTheory.CIC
