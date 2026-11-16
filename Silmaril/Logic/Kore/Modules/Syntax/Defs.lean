module

public import Silmaril.Logic.Kore.Operational.Text.Defs

/-! Monomorphic KORE module syntax. Locations count lexer tokens, not bytes.
The official grammar and validity rules are pinned in
`papers/works/kore-first-order-fragment/kore-syntax.md`. -/
@[expose] public section
namespace Silmaril.Logic.Kore.Modules
open Operational.Text (Token Parser)

structure Location where
  tokenOffset : Nat
  tokenLength : Nat
  deriving Repr

inductive RawPattern where
  | variable (name sort : String)
  | app (name : String) (arguments : List RawPattern)
  | top (sort : String)
  | bottom (sort : String)
  | not (sort : String) (body : RawPattern)
  | and (sort : String) (left right : RawPattern)
  | or (sort : String) (left right : RawPattern)
  | implies (sort : String) (left right : RawPattern)
  | iff (sort : String) (left right : RawPattern)
  | exists (sort name bound : String) (body : RawPattern)
  | forall (sort name bound : String) (body : RawPattern)
  deriving Repr

structure SymbolDeclaration where
  name : String
  arguments : List String
  result : String
  deriving DecidableEq, Repr

structure AliasDeclaration where
  symbol : SymbolDeclaration
  parameters : List (String × String)
  body : RawPattern
  deriving Repr

inductive Declaration (P : Type := RawPattern) (A : Type := AliasDeclaration) where
  | importModule (name : String)
  | sort (name : String)
  | hookedSort (name hook : String)
  | symbol (declaration : SymbolDeclaration)
  | hookedSymbol (declaration : SymbolDeclaration) (hook : String)
  | alias (declaration : A)
  | ruleAxiom (body : P)
  | claim (body : P)
  deriving Repr

structure LocatedDeclaration (P : Type := RawPattern) (A : Type := AliasDeclaration) where
  location : Location
  declaration : Declaration P A
  deriving Repr

structure Module (P : Type := RawPattern) (A : Type := AliasDeclaration) where
  name : String
  location : Location
  declarations : List (LocatedDeclaration P A)
  deriving Repr

structure Definition (P : Type := RawPattern) (A : Type := AliasDeclaration) where
  modules : List (Module P A)
  deriving Repr

namespace Syntax
open Operational.Text

def emptyBraces : Parser Unit := fun ts => do
  let (_, ts) ← punct '{' ts
  punct '}' ts

def emptyAttributes : Parser Unit := fun ts => do
  let (_, ts) ← punct '[' ts
  punct ']' ts

def makeNode (name : String) (sorts : List String) (args : List RawPattern) :
    Option RawPattern :=
  match name, sorts, args with
  | "\\top", [s], [] => some (.top s)
  | "\\bottom", [s], [] => some (.bottom s)
  | "\\not", [s], [p] => some (.not s p)
  | "\\and", [s], [p, q] => some (.and s p q)
  | "\\or", [s], [p, q] => some (.or s p q)
  | "\\implies", [s], [p, q] => some (.implies s p q)
  | "\\iff", [s], [p, q] => some (.iff s p q)
  | "\\exists", [s], [.variable n b, p] => some (.exists s n b p)
  | "\\forall", [s], [.variable n b, p] => some (.forall s n b p)
  | _, [], args =>
      if name.toList.head? == some '\\' || keyword name then none
      else some (.app name args)
  | _, _, _ => none

def pattern : Nat → Parser RawPattern
  | 0, _ => none
  | _ + 1, .name name :: .punctuation ':' :: ts => do
      if keyword name || name.toList.head? == some '\\' then none else do
      let (s, ts) ← sort ts
      return (.variable name s, ts)
  | n + 1, .name name :: .punctuation '{' :: ts => do
      let (sorts, ts) ← list sort '}' (n + 1) ts
      let (_, ts) ← punct '(' ts
      let (args, ts) ← list (pattern n) ')' (n + 1) ts
      return (← makeNode name sorts args, ts)
  | _ + 1, _ => none

def profile : Parser SymbolDeclaration := fun ts => do
  let (name, ts) ← identifier ts
  let (_, ts) ← emptyBraces ts
  let (_, ts) ← punct '(' ts
  let (args, ts) ← list sort ')' (ts.length + 1) ts
  let (_, ts) ← punct ':' ts
  let (result, ts) ← sort ts
  return (⟨name, args, result⟩, ts)

def parameters (name : String) (p : RawPattern) : Option (List (String × String)) := do
  let .app actual args := p | none
  if actual ≠ name then none else
    args.mapM fun p => match p with
      | .variable n s => some (n, s)
      | _ => none

/-- Legacy first-order alias parser, shared by all existing sentence profiles. -/
def aliasDeclaration (fuel : Nat) : Parser AliasDeclaration := fun ts => do
  let (_, rest) ← word "alias" ts
  let (p, rest) ← profile rest
  let (_, rest) ← word "where" rest
  let (lhs, rest) ← pattern fuel rest
  let ps ← parameters p.name lhs
  let (_, rest) ← punct ':' rest
  let (_, rest) ← punct '=' rest
  let (body, rest) ← pattern fuel rest
  let (_, rest) ← emptyAttributes rest
  return (⟨p, ps, body⟩, rest)

def declarationWithAliasAndSorts {P A : Type} (readPattern : Nat → Parser P)
    (readAlias : Nat → Parser A)
    (readSymbol : Bool → Parser (Declaration P A))
    (readSort : Bool → Parser (Declaration P A)) (fuel total : Nat) : Parser (LocatedDeclaration P A) := fun ts => do
  let start := total - ts.length
  let (d, rest) ← match ts with
    | .name "import" :: rest => do
        let (name, rest) ← identifier rest
        let (_, rest) ← emptyAttributes rest
        pure (.importModule name, rest)
    | .name "sort" :: rest => readSort false rest
    | .name "hooked-sort" :: rest => readSort true rest
    | .name "symbol" :: rest => readSymbol false rest
    | .name "hooked-symbol" :: rest => readSymbol true rest
    | .name "alias" :: rest => do
        let (d, rest) ← readAlias fuel (.name "alias" :: rest)
        pure (.alias d, rest)
    | .name "axiom" :: rest => do
        let (_, rest) ← emptyBraces rest
        let (p, rest) ← readPattern fuel rest
        let (_, rest) ← emptyAttributes rest
        pure (.ruleAxiom p, rest)
    | .name "claim" :: rest => do
        let (_, rest) ← emptyBraces rest
        let (p, rest) ← readPattern fuel rest
        let (_, rest) ← emptyAttributes rest
        pure (.claim p, rest)
    | _ => none
  return (⟨⟨start, ts.length - rest.length⟩, d⟩, rest)

def declarationsWithAliasAndSorts {P A : Type} (readPattern : Nat → Parser P)
    (readAlias : Nat → Parser A)
    (readSymbol : Bool → Parser (Declaration P A))
    (readSort : Bool → Parser (Declaration P A)) (total : Nat) : Nat → Parser (List (LocatedDeclaration P A))
  | 0, _ => none
  | _ + 1, .name "endmodule" :: ts => some ([], ts)
  | n + 1, ts => do
      let (d, ts) ← declarationWithAliasAndSorts readPattern readAlias readSymbol readSort (n + 1) total ts
      let (ds, ts) ← declarationsWithAliasAndSorts readPattern readAlias readSymbol readSort total n ts
      return (d :: ds, ts)

def readModuleWithAliasAndSorts {P A : Type} (readPattern : Nat → Parser P)
    (readAlias : Nat → Parser A)
    (readSymbol : Bool → Parser (Declaration P A))
    (readSort : Bool → Parser (Declaration P A)) (fuel total : Nat) : Parser (Module P A) := fun ts => do
  let start := total - ts.length
  let (_, rest) ← word "module" ts
  let (name, rest) ← identifier rest
  let (ds, rest) ← declarationsWithAliasAndSorts readPattern readAlias readSymbol readSort total fuel rest
  let (_, rest) ← emptyAttributes rest
  return (⟨name, ⟨start, ts.length - rest.length⟩, ds⟩, rest)

def modulesWithAliasAndSorts {P A : Type} (readPattern : Nat → Parser P)
    (readAlias : Nat → Parser A)
    (readSymbol : Bool → Parser (Declaration P A))
    (readSort : Bool → Parser (Declaration P A)) (total : Nat) : Nat → List Token → Option (List (Module P A))
  | 0, _ => none
  | _ + 1, [] => some []
  | n + 1, ts => do
      let (m, rest) ← readModuleWithAliasAndSorts readPattern readAlias readSymbol readSort (n + 1) total ts
      return m :: (← modulesWithAliasAndSorts readPattern readAlias readSymbol readSort total n rest)

/-- The exact single hook attribute, shared by builtin and external readers. -/
def hookAttribute : Parser String := fun ts => do
  let (_, ts) ← punct '[' ts
  let (_, ts) ← word "hook" ts
  let (_, ts) ← emptyBraces ts
  let (_, ts) ← punct '(' ts
  let .literal hook :: ts := ts | none
  let (_, ts) ← punct ')' ts
  let (_, ts) ← punct ']' ts
  return (hook, ts)

/-- Metadata-preserving reader parameterized by an explicit hook policy. -/
def hookedSortWith {P A : Type} (accept : String → Bool)
    (hooked : Bool) : Parser (Declaration P A) := fun ts => do
  let (name, ts) ← identifier ts
  let (_, ts) ← emptyBraces ts
  if hooked then do
    let (hook, ts) ← hookAttribute ts
    if accept hook then return (.hookedSort name hook, ts) else none
  else do
    let (_, ts) ← emptyAttributes ts
    return (.sort name, ts)

/-- The profile policy runs after reading the complete hook attribute. -/
def hookedSymbolWith {P A : Type} (accept : String → SymbolDeclaration → Bool)
    (hooked : Bool) : Parser (Declaration P A) := fun ts => do
  let (d, ts) ← profile ts
  if hooked then do
    let (hook, ts) ← hookAttribute ts
    if accept hook d then return (.hookedSymbol d hook, ts) else none
  else do
    let (_, ts) ← emptyAttributes ts
    return (.symbol d, ts)

/-- Default symbol reader: nonempty attributes and hooked declarations reject. -/
def ordinarySymbol {P A : Type} (hooked : Bool) : Parser (Declaration P A) := fun ts => do
  if hooked then none else do
    let (p, rest) ← profile ts
    let (_, rest) ← emptyAttributes rest
    return (.symbol p, rest)

/-- Legacy sort reader rejects hooked sorts and all nonempty attributes. -/
def ordinarySort {P A : Type} (hooked : Bool) : Parser (Declaration P A) := fun ts => do
  if hooked then none else do
    let (name, rest) ← identifier ts
    let (_, rest) ← emptyBraces rest
    let (_, rest) ← emptyAttributes rest
    return (.sort name, rest)

abbrev declarationWithAliasAndSymbols {P A : Type} (p : Nat → Parser P) (a : Nat → Parser A)
    (s : Bool → Parser (Declaration P A)) := declarationWithAliasAndSorts p a s ordinarySort
abbrev declarationsWithAliasAndSymbols {P A : Type} (p : Nat → Parser P) (a : Nat → Parser A)
    (s : Bool → Parser (Declaration P A)) := declarationsWithAliasAndSorts p a s ordinarySort
abbrev readModuleWithAliasAndSymbols {P A : Type} (p : Nat → Parser P) (a : Nat → Parser A)
    (s : Bool → Parser (Declaration P A)) := readModuleWithAliasAndSorts p a s ordinarySort
abbrev modulesWithAliasAndSymbols {P A : Type} (p : Nat → Parser P) (a : Nat → Parser A)
    (s : Bool → Parser (Declaration P A)) := modulesWithAliasAndSorts p a s ordinarySort

abbrev declarationWithAlias {P A : Type} (p : Nat → Parser P) (a : Nat → Parser A) :=
  declarationWithAliasAndSymbols p a ordinarySymbol
abbrev declarationsWithAlias {P A : Type} (p : Nat → Parser P) (a : Nat → Parser A) :=
  declarationsWithAliasAndSymbols p a ordinarySymbol
abbrev readModuleWithAlias {P A : Type} (p : Nat → Parser P) (a : Nat → Parser A) :=
  readModuleWithAliasAndSymbols p a ordinarySymbol
abbrev modulesWithAlias {P A : Type} (p : Nat → Parser P) (a : Nat → Parser A) :=
  modulesWithAliasAndSymbols p a ordinarySymbol

/-- Existing sentence-profile APIs retain first-order alias parsing. -/
abbrev declarationWith {P : Type} (readPattern : Nat → Parser P) :=
  declarationWithAlias readPattern aliasDeclaration
abbrev declarationsWith {P : Type} (readPattern : Nat → Parser P) :=
  declarationsWithAlias readPattern aliasDeclaration
abbrev readModuleWith {P : Type} (readPattern : Nat → Parser P) :=
  readModuleWithAlias readPattern aliasDeclaration
abbrev modulesWith {P : Type} (readPattern : Nat → Parser P) :=
  modulesWithAlias readPattern aliasDeclaration

/-- The original first-order API uses the common envelope parser. Aliases keep
first-order bodies; sentence profiles choose the axiom and claim grammar. -/
abbrev declaration := declarationWith pattern
abbrev declarations := declarationsWith pattern
abbrev readModule := readModuleWith pattern
abbrev modules := modulesWith pattern

/-- Complete definition reader: unsupported constructs and trailing tokens fail. -/
def parse (text : String) : Option Definition := do
  let ts ← tokenize text
  let (_, rest) ← emptyAttributes ts
  let ms ← modules ts.length (ts.length + 1) rest
  if ms.isEmpty then none else some ⟨ms⟩
end Syntax
end Silmaril.Logic.Kore.Modules
