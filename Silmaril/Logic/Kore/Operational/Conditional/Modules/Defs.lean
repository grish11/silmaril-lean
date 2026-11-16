module

public import Silmaril.Logic.Kore.Operational.Conditional.Execution.Defs

/-! A complete module envelope for the conditional constructor profile.
The pinned KORE syntax requires earlier imports and imports before declarations.
All metadata and source declarations are retained; unsupported sentences reject. -/
@[expose] public section
namespace Silmaril.Logic.Kore.Operational.Conditional.Modules
open Silmaril.Logic.Kore.Operational Text

structure Import where
  name : String
  attributes : List Raw
  deriving DecidableEq, Repr

structure SourceModule where
  name : String
  imports : List Import
  declarations : List Declaration
  attributes : List Raw
  deriving DecidableEq, Repr

structure Definition where
  attributes : List Raw
  modules : List SourceModule
  deriving DecidableEq, Repr

def attributes (fuel : Nat) : Parser (List Raw) := fun tokens => do
  let (_, rest) ← punct '[' tokens
  list (raw fuel) ']' fuel rest

def readImport (fuel : Nat) : Parser Import := fun tokens => do
  let (_, rest) ← word "import" tokens
  let (name, rest) ← identifier rest
  let (attrs, rest) ← attributes fuel rest
  return (⟨name, attrs⟩, rest)

/-- Switching to declarations permanently closes the import prefix. -/
def sentences : Nat → Bool → List Import → List Declaration →
    Parser (List Import × List Declaration)
  | 0, _, _, _, _ => none
  | n + 1, importsOpen, imports, declarations, tokens =>
    match tokens with
    | .name "endmodule" :: rest =>
      some ((imports.reverse, declarations.reverse), rest)
    | .name "import" :: _ => do
      if !importsOpen then none else do
      let (i, rest) ← readImport (n + 1) tokens
      sentences n true (i :: imports) declarations rest
    | _ => do
      let (d, rest) ← declaration (n + 1) tokens
      sentences n false imports (d :: declarations) rest

def readModule (fuel : Nat) : Parser SourceModule := fun tokens => do
  let (_, rest) ← word "module" tokens
  let (name, rest) ← identifier rest
  let ((imports, declarations), rest) ← sentences fuel true [] [] rest
  let (attrs, rest) ← attributes fuel rest
  return (⟨name, imports, declarations, attrs⟩, rest)

def readModules : Nat → List Token → Option (List SourceModule)
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, tokens => do
    let (m, rest) ← readModule (n + 1) tokens
    return m :: (← readModules n rest)

/-- Complete definition read: leading attributes, one or more modules, no residue. -/
def parse (input : String) : Option Definition := do
  let tokens ← tokenize input
  let (attrs, rest) ← attributes (tokens.length + 1) tokens
  let modules ← readModules (rest.length + 1) rest
  if modules.isEmpty then none else return ⟨attrs, modules⟩

def Present (modules : List SourceModule) (name : String) : Prop :=
  ∃ m ∈ modules, m.name = name

def Edge (modules : List SourceModule) (source target : String) : Prop :=
  ∃ m ∈ modules, m.name = source ∧ ∃ i ∈ m.imports, i.name = target

/-- Independent raw named-import semantics; no resolver/cache appears here. -/
inductive ImportChain (modules : List SourceModule) : String → String → Prop
  | local {name : String} : Present modules name → ImportChain modules name name
  | importStep {source imported origin : String} :
      Edge modules source imported → ImportChain modules imported origin →
      ImportChain modules source origin

/-- A finite, untrusted witness; its edges are checked against the raw source. -/
inductive Route where
  | local (name : String)
  | via (name : String) (tail : Route)
  deriving DecidableEq, Repr

def Route.start : Route → String
  | .local name => name
  | .via name _ => name

def Route.finish : Route → String
  | .local name => name
  | .via _ tail => tail.finish

def Route.Valid (modules : List SourceModule) : Route → Prop
  | .local name => Present modules name
  | .via name tail => Edge modules name tail.start ∧ tail.Valid modules

instance (modules : List SourceModule) (name : String) : Decidable (Present modules name) := by
  unfold Present
  infer_instance

instance (modules : List SourceModule) (a b : String) : Decidable (Edge modules a b) := by
  unfold Edge
  infer_instance

/-- Structural equations keep this finite source guard executable. -/
def Route.decideValid (modules : List SourceModule) :
    (route : Route) → Decidable (route.Valid modules)
  | .local name => inferInstanceAs (Decidable (Present modules name))
  | .via name tail =>
    letI : Decidable (tail.Valid modules) := Route.decideValid modules tail
    inferInstanceAs (Decidable (Edge modules name tail.start ∧ tail.Valid modules))

instance (modules : List SourceModule) (route : Route) : Decidable (route.Valid modules) :=
  Route.decideValid modules route

def Seen (routes : List Route) (source origin : String) : Prop :=
  ∃ route ∈ routes, route.start = source ∧ route.finish = origin

instance (routes : List Route) (source origin : String) :
    Decidable (Seen routes source origin) := by
  unfold Seen
  infer_instance

/-- Finite soundness witnesses plus all reflexive and one-import closure obligations.
Every obligation is checked during source checking, without external assumptions. -/
def CertificateValid (modules : List SourceModule) (routes : List Route) : Prop :=
  (∀ route ∈ routes, route.Valid modules) ∧
  (∀ m ∈ modules, Seen routes m.name m.name) ∧
  (∀ m ∈ modules, ∀ i ∈ m.imports, ∀ route ∈ routes,
    route.start = i.name → Seen routes m.name route.finish)

instance (modules : List SourceModule) (routes : List Route) :
    Decidable (CertificateValid modules routes) := by
  unfold CertificateValid
  infer_instance

/-- No source declaration or metadata field escapes checking, including modules
outside the selected target's import closure. -/
def ProfileValid (source : Definition) : Prop :=
  source.attributes.all metadataOnly = true ∧
  ∀ m ∈ source.modules,
    m.attributes.all metadataOnly = true ∧
    (∀ i ∈ m.imports, i.attributes.all metadataOnly = true) ∧
    ∀ d ∈ m.declarations, (elaborate d).isSome = true

instance (source : Definition) : Decidable (ProfileValid source) := by
  unfold ProfileValid
  infer_instance

/-- The pinned KORE order contract. A missing, forward or cyclic import fails. -/
def OrderedFrom : List String → List SourceModule → Prop
  | _, [] => True
  | seen, m :: rest =>
    m.name ∉ seen ∧ (∀ i ∈ m.imports, i.name ∈ seen) ∧
    OrderedFrom (m.name :: seen) rest

instance (seen : List String) (modules : List SourceModule) :
    Decidable (OrderedFrom seen modules) := by
  induction modules generalizing seen with
  | nil => exact isTrue True.intro
  | cons m rest ih =>
    change Decidable (m.name ∉ seen ∧
      (∀ i ∈ m.imports, i.name ∈ seen) ∧ OrderedFrom (m.name :: seen) rest)
    letI : Decidable (OrderedFrom (m.name :: seen) rest) := ih _
    infer_instance

/-- Resolve against the previously built prefix. Witnesses may repeat through
diamonds; executable visibility filters the unique raw modules, so declarations
are installed once per source module while local duplicates remain intact. -/
def resolveFrom : List Route → List SourceModule → List Route
  | routes, [] => routes
  | routes, m :: rest =>
    let added := Route.local m.name ::
      m.imports.flatMap (fun i =>
        (routes.filter (fun route => route.start == i.name)).map (Route.via m.name))
    resolveFrom (routes ++ added) rest

def resolve (modules : List SourceModule) : List Route := resolveFrom [] modules

structure CheckedDefinition where
  source : Definition
  routes : List Route
  ordered : OrderedFrom [] source.modules
  profile : ProfileValid source
  certificate : CertificateValid source.modules routes

/-- Every finite validation is part of the executable complete check. -/
def check (input : String) : Option CheckedDefinition := do
  let source ← parse input
  if ordered : OrderedFrom [] source.modules then
    if profile : ProfileValid source then
      let routes := resolve source.modules
      if certificate : CertificateValid source.modules routes then
        return ⟨source, routes, ordered, profile, certificate⟩
      else none
    else none
  else none

/-- Filter the original module list, not the route list: diamond paths deduplicate
modules, but never deduplicate declarations or enabled successor configurations. -/
def CheckedDefinition.visible (p : CheckedDefinition) (target : String) : List SourceModule :=
  p.source.modules.filter (fun m => decide (Seen p.routes target m.name))

def CheckedDefinition.declarations (p : CheckedDefinition) (target : String) :
    List Declaration :=
  (p.visible target).flatMap SourceModule.declarations

def declarationRule (d : Declaration) : Option Rule :=
  if d.kind = .ruleAxiom then (elaborate d).map Prod.snd else none

/-- Checked claims stay in declarations and cannot supply executable transitions. -/
def CheckedDefinition.axioms (p : CheckedDefinition) (target : String) : List Rule :=
  (p.declarations target).filterMap declarationRule

/-- Independent source-origin transition, stated only with raw named imports and
the original declaration elaborator. No resolved rule-list premise appears. -/
inductive SourceStep (source : Definition) (target : String) : Config → Config → Prop
  | rule (m : SourceModule) (member : m ∈ source.modules)
      (visible : ImportChain source.modules target m.name)
      (d : Declaration) (declared : d ∈ m.declarations)
      (isAxiom : d.kind = .ruleAxiom) (Γ : Context) (r : Rule)
      (elaborated : elaborate d = some (Γ, r)) (v : Valuation)
      (coherent : v.x = v.capturedVal) (enabled : r.guard.Holds v.x) :
      SourceStep source target (r.beforeConfig v) (r.afterConfig v)

/-- Unknown target names reject even when the complete source itself checks. -/
def successors? (input target : String) (c : Config) : Option (List Config) := do
  let p ← check input
  if Present p.source.modules target then
    return Execution.successors (p.axioms target) c
  else none

end Silmaril.Logic.Kore.Operational.Conditional.Modules
