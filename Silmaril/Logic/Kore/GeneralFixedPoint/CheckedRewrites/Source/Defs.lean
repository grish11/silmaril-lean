module

public import Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source.Syntax

@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
open Kore.Modules

/-- Syntactic source visibility is checked separately from ambient elaboration. -/
def predicateVisible (scope : Scope) (fuel : Nat) : BooleanTheory.RawPredicate → Bool
  | .top | .bottom => true
  | .equal sort p q | .member sort p q =>
      Kore.Modules.Checking.namedSort scope sort && GeneralFixedPoint.Checking.visible scope fuel p &&
        GeneralFixedPoint.Checking.visible scope fuel q
  | .neg p => predicateVisible scope fuel p
  | .conj p q | .disj p q => predicateVisible scope fuel p && predicateVisible scope fuel q
  | .ex _ bound p => Kore.Modules.Checking.namedSort scope bound && predicateVisible scope fuel p

def visible (scope : Scope) (fuel : Nat) (raw : Raw) : Bool :=
  Kore.Modules.Checking.namedSort scope raw.rewrite.configurationSort &&
    GeneralFixedPoint.Checking.visible scope fuel raw.rewrite.lhs &&
    predicateVisible scope fuel raw.rewrite.guard &&
    GeneralFixedPoint.Checking.visible scope fuel raw.rewrite.rhs

/-- The record retains actual source, checking success and declaring-module
visibility, even when subsequently imported through another module. -/
structure AcceptedRule (ambient : Scope) (cfg : String) where
  source : Raw
  fuel : Nat
  declaringScope : Scope
  checked : CheckedRewrite ambient cfg
  accepted : checkRewrite ambient cfg fuel source.rewrite = some checked
  visible : Source.visible declaringScope fuel source = true

def checkPayload (ambient scope : Scope) (cfg : String) (fuel : Nat)
    (raw : Raw) : Option (AcceptedRule ambient cfg) :=
  if hv : visible scope fuel raw = true then
    match hc : checkRewrite ambient cfg fuel raw.rewrite with
    | none => none
    | some checked => some ⟨raw, fuel, scope, checked, hc, hv⟩
  else none

/-- The enclosing source checker computes origin, location and axiom/claim kind
from the original zipped declaration, not from the selected rule order. -/
structure LocatedRule (ambient : Scope) (cfg : String) where
  origin : Origin
  location : Location
  isClaim : Bool
  payload : AcceptedRule ambient cfg

def localRules (ambient scope : Scope) (cfg : String) (fuel : Nat)
    (m : Module Raw) (claims : Bool) : Option (List (LocatedRule ambient cfg)) :=
  (m.declarations.zipIdx).filterMapM (fun (d, i) => do
    let raw ← match d.declaration, claims with
      | .ruleAxiom raw, false | .claim raw, true => pure (some raw)
      | _, _ => pure none
    match raw with
    | none => pure none
    | some raw => do
        let payload ← checkPayload ambient scope cfg fuel raw
        pure (some ⟨⟨m.name, i⟩, d.location, claims, payload⟩))

structure Import (ambient : Scope) (cfg : String) where
  name : String
  scope : Scope
  axioms : List (LocatedRule ambient cfg)

structure CheckedModule (ambient : Scope) (cfg : String) where
  source : Module Raw
  scope : Scope
  imports : List (Import ambient cfg)
  localAxioms : List (LocatedRule ambient cfg)
  claims : List (LocatedRule ambient cfg)
  fuel : Nat

namespace CheckedModule

/-- List occurrences follow import paths, matching the shared source checker.
Diamonds may repeat the same original origin/location/payload; no deduplication
or uniqueness of operational outcomes is claimed. -/
def axioms {ambient cfg} (m : CheckedModule ambient cfg) : List (LocatedRule ambient cfg) :=
  m.localAxioms ++ m.imports.flatMap Import.axioms

def asImport {ambient cfg} (m : CheckedModule ambient cfg) : Import ambient cfg :=
  ⟨m.source.name, m.scope, m.axioms⟩

/-- This projects actual installed axioms; claims are not part of the list.
Only a successful Package checker equation establishes source provenance. -/
def system {ambient cfg} (m : CheckedModule ambient cfg) : CheckedRewriteSystem ambient cfg :=
  ⟨m.axioms.map (fun rule => ⟨rule.origin, rule.location, rule.payload.checked⟩)⟩

end CheckedModule

/-- Axioms and claims are operational payloads, never matching implications.
Existing declaration profile/ordering/scope helpers determine visibility. -/
def declarationValid (ambient scope : Scope) (cfg : String) (fuel : Nat) :
    Declaration Raw → Bool
  | .sort _ | .importModule _ => true
  | .symbol d => Kore.Modules.Checking.validProfile scope d
  | .hookedSymbol _ _ | .hookedSort _ _ | .alias _ => false
  | .ruleAxiom raw | .claim raw => (checkPayload ambient scope cfg fuel raw).isSome

def checkModule (ambient : Scope) (cfg : String) (fuel : Nat)
    (earlier : List (CheckedModule ambient cfg)) (m : Module Raw) :
    Option (CheckedModule ambient cfg) := do
  if earlier.any (fun p => p.source.name == m.name) then none else do
    let names ← m.orderedImports
    let parents ← names.mapM (fun name =>
      (earlier.find? (fun p => p.source.name == name)).map CheckedModule.asImport)
    let scope := parents.foldl (fun scope p => scope.merge p.scope) m.localScope
    if !m.declarations.all (fun d => declarationValid ambient scope cfg fuel d.declaration)
      then none else do
      let axioms ← localRules ambient scope cfg fuel m false
      let claims ← localRules ambient scope cfg fuel m true
      pure ⟨m, scope, parents, axioms, claims, fuel⟩

structure CheckedDefinition (cfg : String) where
  source : Definition Raw
  ambient : Scope
  modules : List (CheckedModule ambient cfg)

def checkDefinition (cfg : String) (fuel : Nat) (source : Definition Raw) :
    Option (CheckedDefinition cfg) := do
  let result ← Kore.Modules.Checking.traverseDefinitionWith
    (fun ambient earlier m => checkModule ambient cfg fuel earlier m) source
  if !Kore.Modules.Checking.namedSort result.1 cfg then none
  else pure ⟨source, result.1, result.2⟩

/-- Successful complete parsing and source checking are public evidence.
Freely supplying LocatedRule fields is not an accepted-source certificate. -/
structure Package (cfg : String) (fuel : Nat) (text : String) where
  source : Definition Raw
  parsed : Syntax.parse text = some source
  definition : CheckedDefinition cfg
  accepted : checkDefinition cfg fuel source = some definition

def checkText (cfg : String) (fuel : Nat) (text : String) : Option (Package cfg fuel text) :=
  match hp : Syntax.parse text with
  | none => none
  | some source =>
      match hc : checkDefinition cfg fuel source with
      | none => none
      | some definition => some ⟨source, hp, definition, hc⟩

end Silmaril.Logic.Kore.GeneralFixedPoint.CheckedRewrites.Source
