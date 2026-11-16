module

public import Silmaril.Logic.Kore.Modules.Checking.Thms

/-! Executable ordered module/import checking and actual shared presentations.
All modules of a checked definition use its declaration-backed ambient signature;
visibility is checked separately. Claims are judgments, never imported axioms. -/
@[expose] public section
namespace Silmaril.Logic.Kore.Modules
open CategoryTheory Silmaril.Logic.Institution

namespace Declaration

def declaredName {P : Type} : Declaration P → Option String
  | .sort n => some n
  | .symbol d => some d.name
  | .alias d => some d.symbol.name
  | _ => none
end Declaration

namespace Module

def localScope {P : Type} (m : Module P) : Scope :=
  ((m.declarations.zipIdx).foldl (fun scope (d, i) =>
    let origin := Origin.mk m.name i
    match d.declaration with
    | .sort n => {scope with sorts := scope.sorts ++ [(origin, n)]}
    | .symbol s => {scope with symbols := scope.symbols ++ [⟨origin, s⟩]}
    | .alias a => {scope with aliases := scope.aliases ++ [⟨origin, a⟩]}
    | _ => scope) ⟨[], [], []⟩)

/-- An import after any non-import declaration fails. -/
def orderedImports {P : Type} (m : Module P) : Option (List String) :=
  let rec go (seenDeclaration : Bool) : List (LocatedDeclaration P) → Option (List String)
    | [] => some []
    | d :: ds => match d.declaration with
      | .importModule n => if seenDeclaration then none else do
          return n :: (← go false ds)
      | _ => go true ds
  go false m.declarations
end Module

namespace Scope

def merge (a b : Scope) : Scope :=
  ⟨(a.sorts ++ b.sorts).eraseDups, (a.symbols ++ b.symbols).eraseDups,
    b.aliases.foldl (fun acc d =>
      if acc.any (fun old => decide (old.origin = d.origin)) then acc else acc ++ [d]) a.aliases⟩

/-- Actual declaration-preserving signature map; identities survive diamonds. -/
def inclusion {a b : Scope} (h : a.symbols ⊆ b.symbols) : a.signature ⟶ b.signature where
  operations symbol := ⟨symbol.val, h symbol.property.1, symbol.property.2⟩
end Scope

namespace Checking

/-- Every syntactic reference must be in the module's transitive declaration scope.
Typing is a separate intrinsic elaboration check, including actual arities. -/
def visible (scope : Scope) : Nat → RawPattern → Bool
  | 0, _ => false
  | _ + 1, .variable _ s | _ + 1, .top s | _ + 1, .bottom s => namedSort scope s
  | n + 1, .app name ps =>
      (scope.symbols.any (fun d => d.declaration.name == name) ||
        scope.aliases.any (fun d => d.declaration.symbol.name == name)) &&
        ps.all (visible scope n)
  | n + 1, .not s p => namedSort scope s && visible scope n p
  | n + 1, .and s p q | n + 1, .or s p q | n + 1, .implies s p q | n + 1, .iff s p q =>
      namedSort scope s && visible scope n p && visible scope n q
  | n + 1, .exists s _ b p | n + 1, .forall s _ b p =>
      namedSort scope s && namedSort scope b && visible scope n p

def validProfile (scope : Scope) (d : SymbolDeclaration) : Bool :=
  namedSort scope d.result && d.arguments.all (namedSort scope)

def aliasValid (ambient scope : Scope) (fuel : Nat) (a : AliasDeclaration) : Bool :=
  validProfile scope a.symbol && (a.parameters.map Prod.fst).Nodup &&
    a.parameters.map Prod.snd == a.symbol.arguments && visible scope fuel a.body &&
    let Γ := fun i : Fin a.parameters.length => (a.parameters.get i).2
    let vs : List (Binding ambient.signature Γ) :=
      (List.finRange a.parameters.length).map
        (fun i => ⟨(a.parameters.get i).1, Γ i, .evar i⟩)
    (elaborate ambient fuel vs a.symbol.result a.body).isSome

/-- A sentence profile shares the complete declaration/import checker while
choosing its raw pattern grammar, visibility check and institution. -/
structure SentenceProfile where
  Raw : Type
  institution : Algebraic.ManySorted.Signature String ⥤ Room.{0, 0, 1}
  sentence : (ambient : Scope) → Nat → Raw →
    Option ((institution.obj ambient.signature).Sen)
  visible : Scope → Nat → Raw → Bool
  allowAliases : Bool

def firstOrderProfile : SentenceProfile :=
  ⟨RawPattern, FirstOrder.institution String, sentence, visible, true⟩

def validateDeclarationWith (profile : SentenceProfile) (ambient scope : Scope)
    (fuel : Nat) : Declaration profile.Raw → Bool
  | .sort _ | .importModule _ => true
  | .symbol d => validProfile scope d
  | .hookedSymbol _ _ | .hookedSort _ _ => false
  | .alias a => profile.allowAliases && aliasValid ambient scope fuel a
  | .ruleAxiom p | .claim p =>
      profile.visible scope fuel p && (profile.sentence ambient fuel p).isSome

abbrev validateDeclaration := validateDeclarationWith firstOrderProfile

/-- A checked axiom/claim carries its original source identity and location. -/
structure CheckedSentence (ambient : Scope)
    (profile : SentenceProfile := firstOrderProfile) where
  origin : Origin
  location : Location
  raw : profile.Raw
  fuel : Nat
  sentence : (profile.institution.obj ambient.signature).Sen
  elaborated : profile.sentence ambient fuel raw = some sentence

structure Import (ambient : Scope) (profile : SentenceProfile := firstOrderProfile) where
  name : String
  scope : Scope
  axioms : List (CheckedSentence ambient profile)

structure CheckedModule (ambient : Scope)
    (profile : SentenceProfile := firstOrderProfile) where
  source : Module profile.Raw
  scope : Scope
  imports : List (Import ambient profile)
  localAxioms : List (CheckedSentence ambient profile)
  claims : List (CheckedSentence ambient profile)
  fuel : Nat
  validated : source.declarations.all
    (fun d => validateDeclarationWith profile ambient scope fuel d.declaration) = true

namespace CheckedModule

def axioms {ambient : Scope} {profile : SentenceProfile} (m : CheckedModule ambient profile) : List (CheckedSentence ambient profile) :=
  m.localAxioms ++ m.imports.flatMap Import.axioms

def asImport {ambient : Scope} {profile : SentenceProfile} (m : CheckedModule ambient profile) : Import ambient profile :=
  ⟨m.source.name, m.scope, m.axioms⟩

def axiomSet {ambient : Scope} {profile : SentenceProfile} (m : CheckedModule ambient profile) :
    Set ((profile.institution.obj ambient.signature).Sen) :=
  {p | ∃ d ∈ m.axioms, d.sentence = p}

def presentation {ambient : Scope} {profile : SentenceProfile} (m : CheckedModule ambient profile) :
    Presentation profile.institution := ⟨ambient.signature, m.axiomSet⟩

def theory {ambient : Scope} {profile : SentenceProfile} (m : CheckedModule ambient profile) : Theory profile.institution :=
  (Silmaril.Logic.Institution.Theory.ofPresentation profile.institution).obj
    m.presentation

/-- Satisfaction of claims is evaluated against models of the axiom presentation. -/
def Proves {ambient : Scope} {profile : SentenceProfile} (m : CheckedModule ambient profile)
    (p : (profile.institution.obj ambient.signature).Sen) : Prop :=
  (profile.institution.obj ambient.signature).Entails m.axiomSet p
end CheckedModule


def localSentencesWith (profile : SentenceProfile) (ambient : Scope) (fuel : Nat)
    (m : Module profile.Raw) (claims : Bool) :
    Option (List (CheckedSentence ambient profile)) :=
  (m.declarations.zipIdx).filterMapM (fun (d, i) => do
    let p ← match d.declaration, claims with
      | .ruleAxiom p, false | .claim p, true => pure (some p)
      | _, _ => pure none
    match p with
    | none => pure none
    | some p => do
        match eq : profile.sentence ambient fuel p with
        | none => none
        | some checked => pure (some ⟨⟨m.name, i⟩, d.location, p, fuel, checked, eq⟩))

/-- Imports resolve only against modules already checked in this definition.
The returned imports retain cached axiom identity, including shared diamonds. -/
def checkModuleWith (profile : SentenceProfile) (ambient : Scope) (fuel : Nat)
    (earlier : List (CheckedModule ambient profile))
    (m : Module profile.Raw) : Option (CheckedModule ambient profile) := do
  if earlier.any (fun p => p.source.name == m.name) then none else do
    let names ← m.orderedImports
    let parents ← names.mapM (fun name =>
      (earlier.find? (fun p => p.source.name == name)).map CheckedModule.asImport)
    let scope := parents.foldl (fun scope p => scope.merge p.scope) m.localScope
    if valid : m.declarations.all (fun d => validateDeclarationWith profile ambient scope fuel d.declaration) = true
      then do
      let axioms ← localSentencesWith profile ambient fuel m false
      let claims ← localSentencesWith profile ambient fuel m true
      pure ⟨m, scope, parents, axioms, claims, fuel, valid⟩
    else none

structure CheckedDefinition (profile : SentenceProfile := firstOrderProfile) where
  source : Definition profile.Raw
  ambient : Scope
  modules : List (CheckedModule ambient profile)

/-- Institution-independent ordered definition traversal. Payload checking is
supplied by the caller; declaration identity and global name policy are shared. -/
def traverseDefinitionWith {P : Type} {C : Scope → Type}
    (check : (ambient : Scope) → List (C ambient) → Module P → Option (C ambient))
    (d : Definition P) : Option (Σ ambient : Scope, List (C ambient)) := do
  if d.modules.isEmpty then none else do
    let names := d.modules.flatMap (fun m =>
      m.declarations.filterMap (fun d => d.declaration.declaredName))
    if !names.Nodup ||
        !names.all (fun name => name.toList.head?.any Operational.Text.letter) ||
        !d.modules.all (fun m => m.name.toList.head?.any Operational.Text.letter)
      then none else do
      let ambient := d.modules.foldl (fun scope m => scope.merge m.localScope) ⟨[], [], []⟩
      let ms ← d.modules.foldlM (fun earlier m => do
        let checked ← check ambient earlier m
        pure (earlier ++ [checked])) []
      pure ⟨ambient, ms⟩

/-- Check global declaration uniqueness before resolving any source scope,
using the same ordered traversal as other checked operational payloads. -/
def checkDefinitionWith (profile : SentenceProfile) (fuel : Nat)
    (d : Definition profile.Raw) : Option (CheckedDefinition profile) := do
  let result ← traverseDefinitionWith
    (fun ambient earlier m => checkModuleWith profile ambient fuel earlier m) d
  pure ⟨d, result.1, result.2⟩

abbrev localSentences := localSentencesWith firstOrderProfile
abbrev checkModule := checkModuleWith firstOrderProfile
abbrev checkDefinition := checkDefinitionWith firstOrderProfile

/-- Complete real text → AST → checked intrinsic module presentations. -/
def checkText (fuel : Nat) (text : String) : Option CheckedDefinition := do
  checkDefinition fuel (← Syntax.parse text)
end Checking
end Silmaril.Logic.Kore.Modules
