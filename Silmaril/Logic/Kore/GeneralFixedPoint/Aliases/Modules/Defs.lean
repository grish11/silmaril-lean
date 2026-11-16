module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.Institution.Defs
public import Silmaril.Logic.Kore.GeneralFixedPoint.Modules.Defs

/-! Complete monomorphic module/import envelope for terminating general aliases.
The original first-order and alias-free general profiles retain their behavior. -/
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Aliases
open CategoryTheory Silmaril.Logic.Institution

abbrev SourceModule := Kore.Modules.Module RawPattern Declaration
abbrev SourceDefinition := Kore.Modules.Definition RawPattern Declaration

structure NamedAlias where
  origin : Kore.Modules.Origin
  declaration : Declaration

structure ModuleScope where
  base : Kore.Modules.Scope
  aliases : List NamedAlias

namespace ModuleScope

def merge (a b : ModuleScope) : ModuleScope :=
  ⟨a.base.merge b.base, b.aliases.foldl (fun acc d =>
    if acc.any (fun old => decide (old.origin = d.origin)) then acc else acc ++ [d]) a.aliases⟩

def table (s : ModuleScope) : List Declaration := s.aliases.map NamedAlias.declaration
end ModuleScope

namespace Checking
open Kore.Modules.Checking

/-- Independent source visibility; the ambient compiler table does not confer
permission to use declarations outside transitive imports. -/
def visible (scope : ModuleScope) : Nat → RawPattern → Bool
  | 0, _ => false
  | _ + 1, .domainValue _ _ => false
  | _ + 1, .evar _ s | _ + 1, .svar _ s | _ + 1, .top s | _ + 1, .bottom s =>
      namedSort scope.base s
  | n + 1, .app name ps =>
      (scope.base.symbols.any (fun d => d.declaration.name == name) ||
        scope.aliases.any (fun d => d.declaration.symbol.name == name)) && ps.all (visible scope n)
  | n + 1, .neg s p => namedSort scope.base s && visible scope n p
  | n + 1, .conj s p q | n + 1, .disj s p q =>
      namedSort scope.base s && visible scope n p && visible scope n q
  | n + 1, .ex s _ b p | n + 1, .all s _ b p =>
      namedSort scope.base s && namedSort scope.base b && visible scope n p
  | n + 1, .mu _ s p | n + 1, .nu _ s p => namedSort scope.base s && visible scope n p

def localScope (m : SourceModule) : ModuleScope :=
  (m.declarations.zipIdx).foldl (fun scope (d, i) =>
    let origin := Kore.Modules.Origin.mk m.name i
    match d.declaration with
    | .sort n => {scope with base.sorts := scope.base.sorts ++ [(origin, n)]}
    | .symbol s => {scope with base.symbols := scope.base.symbols ++ [⟨origin, s⟩]}
    | .alias a => {scope with aliases := scope.aliases ++ [⟨origin, a⟩]}
    | _ => scope) ⟨⟨[], [], []⟩, []⟩

def orderedImports (m : SourceModule) : Option (List String) :=
  let rec go (seen : Bool) : List (Kore.Modules.LocatedDeclaration RawPattern Declaration) →
      Option (List String)
    | [] => some []
    | d :: ds => match d.declaration with
      | .importModule n => if seen then none else return n :: (← go false ds)
      | _ => go true ds
  go false m.declarations

def resultSort (scope : Kore.Modules.Scope) (aliases : List Declaration) : RawPattern → Option String
  | .app name _ =>
      match scope.symbols.find? (fun d => d.declaration.name == name) with
      | some d => some d.declaration.result
      | none => (aliases.find? (fun d => d.symbol.name == name)).map (fun d => d.symbol.result)
  | raw => GeneralFixedPoint.Checking.resultSort scope raw

def checkedSentence (scope : Kore.Modules.Scope) (aliases : List Declaration)
    (fuel : Nat) (raw : RawPattern) : Option (CheckedSentence scope) := do
  let sets := (GeneralFixedPoint.Checking.freeNames true fuel [] raw).eraseDups
  let objects := (GeneralFixedPoint.Checking.freeNames false fuel [] raw).eraseDups
  let s ← resultSort scope aliases raw
  match accepted : elaborate scope aliases fuel sets objects s raw with
  | none => none
  | some typed => if admitted : typed.admissible = true then
      some ⟨aliases, fuel, sets, objects, s, raw, typed, accepted, admitted⟩ else none

/-- Every alias is checked, even when unused. Compiling in exactly the declared
formals enforces closure; bounded expansion rejects cycles and excessive depth. -/
def aliasValid (ambient : Kore.Modules.Scope) (aliases : List Declaration)
    (scope : ModuleScope) (fuel : Nat) (d : Declaration) : Bool :=
  d.valid scope.base && visible scope fuel d.body &&
    match elaborate ambient aliases fuel (d.names true) (d.names false) d.symbol.result d.body with
    | none => false
    | some body => body.admissible

def validate (ambient : Kore.Modules.Scope) (aliases : List Declaration)
    (scope : ModuleScope) (fuel : Nat) : Kore.Modules.Declaration RawPattern Declaration → Bool
  | .sort _ | .importModule _ => true
  | .symbol d => validProfile scope.base d
  | .hookedSymbol _ _ | .hookedSort _ _ => false
  | .alias d => aliasValid ambient aliases scope fuel d
  | .ruleAxiom p | .claim p =>
      visible scope fuel p && (checkedSentence ambient aliases fuel p).isSome

structure LocatedSentence (ambient : Kore.Modules.Scope) where
  origin : Kore.Modules.Origin
  location : Kore.Modules.Location
  source : CheckedSentence ambient

structure Import (ambient : Kore.Modules.Scope) where
  name : String
  scope : ModuleScope
  axioms : List (LocatedSentence ambient)

structure CheckedModule (ambient : Kore.Modules.Scope) where
  source : SourceModule
  scope : ModuleScope
  imports : List (Import ambient)
  localAxioms : List (LocatedSentence ambient)
  claims : List (LocatedSentence ambient)
  aliases : List Declaration
  fuel : Nat
  validated : source.declarations.all (fun d => validate ambient aliases scope fuel d.declaration) = true

namespace CheckedModule

def axioms {ambient : Kore.Modules.Scope} (m : CheckedModule ambient) : List (LocatedSentence ambient) :=
  m.localAxioms ++ m.imports.flatMap Import.axioms

def asImport {ambient : Kore.Modules.Scope} (m : CheckedModule ambient) : Import ambient :=
  ⟨m.source.name, m.scope, m.axioms⟩

def axiomSet {ambient : Kore.Modules.Scope} (m : CheckedModule ambient) :
    Set (Sentence ambient.signature) := {p | ∃ d ∈ m.axioms, d.source.install = p}

def presentation {ambient : Kore.Modules.Scope} (m : CheckedModule ambient) :
    Silmaril.Logic.Institution.Presentation institution := ⟨ambient.signature, m.axiomSet⟩

def theory {ambient : Kore.Modules.Scope} (m : CheckedModule ambient) :
    Silmaril.Logic.Institution.Theory institution :=
  (Silmaril.Logic.Institution.Theory.ofPresentation institution).obj m.presentation

def Proves {ambient : Kore.Modules.Scope} (m : CheckedModule ambient)
    (p : Sentence ambient.signature) : Prop := (institution.obj ambient.signature).Entails m.axiomSet p
end CheckedModule

def localSentences (ambient : Kore.Modules.Scope) (aliases : List Declaration)
    (fuel : Nat) (m : SourceModule) (claims : Bool) : Option (List (LocatedSentence ambient)) :=
  (m.declarations.zipIdx).filterMapM (fun (d, i) => do
    let p ← match d.declaration, claims with
      | .ruleAxiom p, false | .claim p, true => pure (some p)
      | _, _ => pure none
    match p with
    | none => pure none
    | some p => return some ⟨⟨m.name, i⟩, d.location, ← checkedSentence ambient aliases fuel p⟩)

def checkModule (ambient : Kore.Modules.Scope) (aliases : List Declaration) (fuel : Nat)
    (earlier : List (CheckedModule ambient)) (m : SourceModule) : Option (CheckedModule ambient) := do
  if earlier.any (fun p => p.source.name == m.name) then none else do
    let names ← orderedImports m
    let parents ← names.mapM (fun name =>
      (earlier.find? (fun p => p.source.name == name)).map CheckedModule.asImport)
    let scope := parents.foldl (fun scope p => scope.merge p.scope) (localScope m)
    if valid : m.declarations.all (fun d => validate ambient aliases scope fuel d.declaration) = true then do
      let axioms ← localSentences ambient aliases fuel m false
      let claims ← localSentences ambient aliases fuel m true
      return ⟨m, scope, parents, axioms, claims, aliases, fuel, valid⟩
    else none

structure CheckedDefinition where
  source : SourceDefinition
  ambient : Kore.Modules.Scope
  aliases : List Declaration
  modules : List (CheckedModule ambient)

def declaredName : Kore.Modules.Declaration RawPattern Declaration → Option String
  | .sort n => some n
  | .symbol d => some d.name
  | .alias d => some d.symbol.name
  | _ => none

def checkDefinition (fuel : Nat) (d : SourceDefinition) : Option CheckedDefinition := do
  if d.modules.isEmpty then none else do
    let names := d.modules.flatMap (fun m => m.declarations.filterMap
      (fun d => declaredName d.declaration))
    if !names.Nodup ||
        !names.all (fun name => name.toList.head?.any Operational.Text.letter) ||
        !d.modules.all (fun m => m.name.toList.head?.any Operational.Text.letter) then none else do
      let ambient : ModuleScope := d.modules.foldl (fun scope m => scope.merge (localScope m)) ⟨⟨[], [], []⟩, []⟩
      let ms ← d.modules.foldlM (fun earlier m => do
        let checked ← checkModule ambient.base ambient.table fuel earlier m
        pure (earlier ++ [checked])) []
      return ⟨d, ambient.base, ambient.table, ms⟩
end Checking

namespace Modules

def parse (text : String) : Option SourceDefinition := do
  let ts ← Kore.FixedPoint.Syntax.lex (text.toList.length + 1) text.toList []
  let (_, rest) ← Kore.Modules.Syntax.emptyAttributes ts
  let ms ← Kore.Modules.Syntax.modulesWithAlias GeneralFixedPoint.Syntax.pattern
    Syntax.declaration ts.length (ts.length + 1) rest
  if ms.isEmpty then none else some ⟨ms⟩

def checkText (fuel : Nat) (text : String) : Option Checking.CheckedDefinition := do
  Checking.checkDefinition fuel (← parse text)
end Modules
end Silmaril.Logic.Kore.GeneralFixedPoint.Aliases
