module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Aliases.Modules.Thms

/-! A bounded builtin extension of the existing general module grammar.
All ordinary declarations, imports, aliases and general fixed points retain the
common envelope. Only domain values and exact hook attributes are added. -/
-- Configurable builtin names intentionally have a canonical fallback instance.
set_option linter.concreteInstances false
@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
open Operational.Text

/-- The semantic builtin sort names. Distinctness rules out identifying Int and Bool.
The canonical instance preserves the earlier frontend as a specialization. -/
class SortBindings where
  intSort : String
  boolSort : String
  distinct : intSort ≠ boolSort
  deriving Repr

instance (priority := low) canonicalSortBindings : SortBindings :=
  ⟨"SortInt", "SortBool", by decide⟩

variable [sorts : SortBindings]

inductive Literal where
  | integer (value : Int)
  | boolean (value : Bool)
  deriving DecidableEq, Repr

def Literal.sort : Literal → String
  | .integer _ => sorts.intSort
  | .boolean _ => sorts.boolSort

/-- Exposed signed-decimal reader: no whitespace, plus sign or separators.
The accumulator is an actual unbounded natural number. -/
def decimalDigits : List Char → Nat → Option Nat
  | [], value => some value
  | c :: cs, value =>
      if '0' ≤ c && c ≤ '9' then
        decimalDigits cs (10 * value + (c.toNat - '0'.toNat))
      else none

def decimalNatural : List Char → Option Nat
  | [] => none
  | c :: cs => decimalDigits (c :: cs) 0

def decimalInteger (text : String) : Option Int :=
  match text.toList with
  | '-' :: cs => (decimalNatural cs).map (fun n => -(Int.ofNat n))
  | cs => (decimalNatural cs).map Int.ofNat

def Literal.parse (sort text : String) : Option Literal :=
  if sort = sorts.intSort then (decimalInteger text).map Literal.integer
  else if sort = sorts.boolSort then
    if text = "true" then some (.boolean true)
    else if text = "false" then some (.boolean false) else none
  else none

inductive Hook where
  | intEq
  | boolNot
  deriving DecidableEq, Repr

def Hook.parse : String → Option Hook
  | "INT.eq" => some .intEq
  | "BOOL.not" => some .boolNot
  | _ => none

def Hook.arguments : Hook → List String
  | .intEq => [sorts.intSort, sorts.intSort]
  | .boolNot => [sorts.boolSort]

def Hook.result (_ : Hook) : String := sorts.boolSort

def Hook.valid (h : Hook) (d : Kore.Modules.SymbolDeclaration) : Bool :=
  d.arguments == h.arguments && d.result == h.result

namespace Syntax

def patternWith (acceptLiteral : String → String → Bool) : Nat → Parser RawPattern
  | 0, _ => none
  | _ + 1, .name "\\dv" :: .punctuation '{' :: ts => do
      let (s, ts) ← sort ts
      let (_, ts) ← punct '}' ts
      let (_, ts) ← punct '(' ts
      let .literal text :: ts := ts | none
      let (_, ts) ← punct ')' ts
      if acceptLiteral s text then some (.domainValue s text, ts) else none
  | _ + 1, .name name :: .punctuation ':' :: ts => do
      let (s, ts) ← sort ts
      if name.toList.head? == some '@' then return (.svar name s, ts)
      else if GeneralFixedPoint.Syntax.ordinary name then return (.evar name s, ts)
      else none
  | n + 1, .name name :: .punctuation '{' :: ts => do
      let (sorts, ts) ← list sort '}' (n + 1) ts
      let (_, ts) ← punct '(' ts
      let (args, ts) ← list (patternWith acceptLiteral n) ')' (n + 1) ts
      return (← GeneralFixedPoint.Syntax.makeNode name sorts args, ts)
  | _ + 1, _ => none

abbrev pattern := patternWith (fun s text => (Literal.parse s text).isSome)

def aliasDeclarationWith (readPattern : Nat → Parser RawPattern) (fuel : Nat) : Parser Aliases.Declaration := fun ts => do
  let (_, ts) ← word "alias" ts
  let (symbol, ts) ← Kore.Modules.Syntax.profile ts
  let (_, ts) ← word "where" ts
  let (lhs, ts) ← readPattern fuel ts
  let parameters ← Aliases.Syntax.parameters symbol.name lhs
  let (_, ts) ← punct ':' ts
  let (_, ts) ← punct '=' ts
  let (body, ts) ← readPattern fuel ts
  let (_, ts) ← Kore.Modules.Syntax.emptyAttributes ts
  return (⟨symbol, parameters, body⟩, ts)

abbrev aliasDeclaration := aliasDeclarationWith pattern

/-- Unknown hooks, wrong profiles and every other nonempty attribute reject. -/
def symbolWith (validProfile : Hook → Kore.Modules.SymbolDeclaration → Bool) :
    Bool → Parser (Kore.Modules.Declaration RawPattern Aliases.Declaration) :=
  Kore.Modules.Syntax.hookedSymbolWith (fun name d =>
    (Hook.parse name).any (fun h => validProfile h d))

abbrev symbol := symbolWith Hook.valid

def parse (text : String) : Option Aliases.SourceDefinition := do
  let ts ← FixedPoint.Syntax.lex (text.toList.length + 1) text.toList []
  let (_, rest) ← Kore.Modules.Syntax.emptyAttributes ts
  let ms ← Kore.Modules.Syntax.modulesWithAliasAndSymbols pattern aliasDeclaration symbol
    ts.length (ts.length + 1) rest
  if ms.isEmpty then none else some ⟨ms⟩
end Syntax
end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins
