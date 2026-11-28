module

public import Silmaril.Logic.Temporal.TLA.DataElab.Defs
public import Silmaril.Logic.Temporal.TLA.Resolution.Levels.Defs
public import Silmaril.Logic.Temporal.TLA.Surface.Parser.Defs

/-! Scoped, constant-level TLA+ proof obligations over the data denotation. -/

namespace Silmaril.Logic.Temporal.TLA.ProofFrontEnd

open Resolution DataElab

universe u

public section

abbrev noPrimitives : DataElab.ExternalSignature := fun _ => none

abbrev Proposition := CheckedExpr noPrimitives

structure Interpretation (V : Type u) where
  operations : DataOperations V
  booleans : Booleans V

/-- Truth in a single interpretation of the landed data semantics. -/
@[expose] noncomputable def Proposition.holds {V : Type u} (proposition : Proposition)
    (model : Interpretation V) (valuation : Valuation V) : Prop :=
  proposition.eval model.operations model.booleans (fun _ _ admitted => nomatch admitted)
    valuation = model.booleans.trueValue

structure Assumption where
  unit : Nat
  name : Option Surface.Ident
  proposition : Proposition

/-- Only previously declared module facts have citation identities in this profile. -/
inductive FactRef where
  | assumption (unit : Nat)
  | theoremDecl (unit : Nat)
  deriving DecidableEq, Repr

/-- The status of the source proof text after scope checking. -/
inductive Unresolved where
  | missing
  | omitted
  | obvious
  | byFacts (only : Bool) (facts : List FactRef)
  deriving DecidableEq, Repr

structure Obligation where
  private mk ::
  unit : Nat
  name : Option Surface.Ident
  assumptions : List Assumption
  hypotheses : List Proposition
  goal : Proposition
  sourceProof : Unresolved

structure Context where
  private mk ::
  assumptions : List Assumption
  theorems : List Obligation

/-- A theorem judgment under its preceding module assumptions and local hypotheses,
for every valuation in the chosen data interpretation. -/
@[expose] def Obligation.Valid {V : Type u} (obligation : Obligation)
    (model : Interpretation V) : Prop :=
  ∀ valuation : Valuation V,
    (∀ fact ∈ obligation.assumptions, fact.proposition.holds model valuation) →
    (∀ hypothesis ∈ obligation.hypotheses, hypothesis.holds model valuation) →
    obligation.goal.holds model valuation

/-- Evidence provided by a Lean caller for the denoted judgment. -/
structure SuppliedEvidence {V : Type u} (obligation : Obligation)
    (model : Interpretation V) : Prop where
  valid : obligation.Valid model

/-- Evidence produced by the exact named-assumption rule. -/
structure ExactCertificate (obligation : Obligation) where
  private mk ::
  premise : Assumption
  inScope : premise ∈ obligation.assumptions
  termEq : premise.proposition.term = obligation.goal.term

inductive Diagnostic where
  | parse (error : Surface.Parser.Diagnostic)
  | imports
  | unsupportedUnit (unit : Nat)
  | unsupportedStatement (unit : Nat)
  | unsupportedProof (unit : Nat)
  | unsupportedCitation (unit : Nat)
  | nameConflict (unit : Nat) (name : Surface.Ident)
  | factNotInScope (unit : Nat) (name : Surface.Ident)
  | resolution (error : Resolution.Diagnostic)
  | levels (error : Levels.Diagnostic)
  | missingLevel (site : Site)
  | expectedConstant (site : Site) (actual : Levels.Level)
  | lowering (error : DataElab.Diagnostic)
  deriving Repr

end

open Surface

private inductive StatementKind where
  | assumption
  | theoremDecl (proof : Option Proof)

private structure StatementPlan where
  unit : Nat
  kind : StatementKind
  name : Option Ident
  goal : Nat
  hypotheses : List Nat

/-- A generated identifier containing a colon cannot be named by the parser. -/
private def expressionUnit (index : Nat) (name : Option Ident) (body : Expr) : ModuleUnit :=
  .definition (.operator .ordinary (.ident (name.getD s!"proof:{index}") []) body)

/-- Project source expressions to nullary definitions for the existing resolver and
lowerer. Local hypotheses get fresh private-to-the-projection names. -/
private def project (source : Surface.Module) :
    Except Diagnostic (Surface.Module × List StatementPlan) := do
  unless source.extendsModules.isEmpty do throw .imports
  let mut projected := #[]
  let mut plans := []
  let mut names : List Ident := []
  for (unit, index) in source.units.zipIdx do
    let (kind, name, hypotheses, goal) ← match unit with
      | .assumption name body => pure (.assumption, name, [], body)
      | .theoremDecl ⟨name, statement, proof⟩ =>
        match statement with
        | .expr goal => pure (.theoremDecl proof, name, [], goal)
        | .assumeProve .plain hypotheses .plain goal =>
          let hypotheses ← hypotheses.mapM fun
            | .statement (.expr expression) => pure expression
            | _ => throw (.unsupportedStatement index)
          pure (.theoremDecl proof, name, hypotheses, goal)
        | _ => throw (.unsupportedStatement index)
      | .constants _ | .variables _ | .definition (.operator ..) =>
        projected := projected.push unit
        continue
      | _ => throw (.unsupportedUnit index)
    if let some name := name then
      if names.contains name then throw (.nameConflict index name)
      names := name :: names
    let start := projected.size
    for hypothesis in hypotheses do
      projected := projected.push (expressionUnit projected.size none hypothesis)
    let goalIndex := projected.size
    -- An ASSUME/PROVE name denotes a rule and cannot be used as an expression.
    projected := projected.push (expressionUnit goalIndex
      (if hypotheses.isEmpty then name else none) goal)
    plans := ⟨index, kind, name, goalIndex, List.range' start hypotheses.length⟩ :: plans
  return ({ source with units := projected.toList }, plans.reverse)

private def resolveProof (unit : Nat) (known : List (Ident × FactRef)) :
    Option Proof → Except Diagnostic Unresolved
  | none => pure .missing
  | some .omitted => pure .omitted
  | some .obvious => pure .obvious
  | some (.steps ..) => throw (.unsupportedProof unit)
  | some (.byFacts only citations) => do
    unless citations.defs.isEmpty && !citations.facts.isEmpty do
      throw (.unsupportedCitation unit)
    let facts ← citations.facts.mapM fun
      | .expr (.ref (.operator (.ident name)) [] []) =>
        match known.lookup name with
        | some fact => pure fact
        | none => throw (.factNotInScope unit name)
      | _ => throw (.unsupportedCitation unit)
    return .byFacts only facts

private def lower (registry : CheckedRegistry) (levels : Levels.CheckedLevels)
    (maxDepth index : Nat) : Except Diagnostic Proposition := do
  let site : Site := ⟨registry.root, [.unit index]⟩
  let id := BindingId.declared site
  let some level := levels.operatorAt id | throw (.missingLevel site)
  unless level.result.floor = .constant do throw (.expectedConstant site level.result.floor)
  (DataElab.lowerDefinition registry noPrimitives maxDepth id).mapError .lowering

/-- Prepare obligations for a single parsed source module. Source proof text
is scoped here and can be passed to the separate exact checker. -/
public def prepare (source : String) (maxDepth : Nat := 64) : Except Diagnostic Context := do
  let parsed ← (Surface.Parser.parseModule source).mapError .parse
  let (projected, plans) ← project parsed
  let registry ← (Resolution.resolveWith .levelSyntax
    [(parsed.name, .parsed projected [])] parsed.name).mapError .resolution
  let levels ← (Levels.check registry).mapError .levels
  let mut known := []
  let mut assumptions := []
  let mut theorems := []
  for plan in plans do
    if let some name := plan.name then
      if !plan.hypotheses.isEmpty &&
          ((registry.moduleAt parsed.name).bind (·.bindingAt (.ident name))).isSome then
        throw (.nameConflict plan.unit name)
    let goal ← lower registry levels maxDepth plan.goal
    let fact ← match plan.kind with
      | .assumption =>
        assumptions := ⟨plan.unit, plan.name, goal⟩ :: assumptions
        pure (.assumption plan.unit)
      | .theoremDecl proof =>
        let hypotheses ← plan.hypotheses.mapM (lower registry levels maxDepth)
        let proof ← resolveProof plan.unit known proof
        theorems := ⟨plan.unit, plan.name, assumptions.reverse, hypotheses, goal, proof⟩ :: theorems
        pure (.theoremDecl plan.unit)
    if let some name := plan.name then
      known := (name, fact) :: known
  return ⟨assumptions.reverse, theorems.reverse⟩

/-- Compare a small fragment of expanded expressions. Every successful match
contains an equality of the actual evaluated terms. -/
private def matchTerm (left right : Term noPrimitives) : Option (PLift (left = right)) :=
  match left, right with
  | .rigid x, .rigid y => if h : x = y then some ⟨congrArg Term.rigid h⟩ else none
  | .numeral x, .numeral y => if h : x = y then some ⟨congrArg Term.numeral h⟩ else none
  | .boolean x, .boolean y => if h : x = y then some ⟨congrArg Term.boolean h⟩ else none
  | .eq n l r, .eq m l' r' => do
    if hn : n = m then
      let ⟨hl⟩ ← matchTerm l l'
      let ⟨hr⟩ ← matchTerm r r'
      return ⟨by
        cases hn
        cases hl
        cases hr
        rfl⟩
    else none
  | _, _ => none

/-- Check a leaf with exactly one named module assumption. The citation selects
a candidate premise; a Lean term equality certifies the application of the rule. -/
public def Obligation.checkExact (obligation : Obligation) : Option (ExactCertificate obligation) := do
  let .byFacts _ [.assumption unit] := obligation.sourceProof | none
  let some ⟨premise, inScope⟩ := obligation.assumptions.attach.find? (·.val.unit == unit) | none
  let ⟨termEq⟩ ← matchTerm premise.proposition.term obligation.goal.term
  return ⟨premise, inScope, termEq⟩

end Silmaril.Logic.Temporal.TLA.ProofFrontEnd
