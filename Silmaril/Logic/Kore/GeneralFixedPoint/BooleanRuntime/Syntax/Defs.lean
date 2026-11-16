module

public import Silmaril.Logic.Kore.GeneralFixedPoint.HookedSorts.Modules.Defs

/-! Complete Boolean builtin profile. Existing readers retain their grammar.
Original hook declarations and exact domain-value annotations are retained. -/
@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.BooleanRuntime
open Operational.Text

inductive BinaryHook where
  | and | or | andThen | orElse | xor | implies | ne | eq
  deriving DecidableEq, Repr

def BinaryHook.parse : String → Option BinaryHook
  | "BOOL.and" => some .and
  | "BOOL.or" => some .or
  | "BOOL.andThen" => some .andThen
  | "BOOL.orElse" => some .orElse
  | "BOOL.xor" => some .xor
  | "BOOL.implies" => some .implies
  | "BOOL.ne" => some .ne
  | "BOOL.eq" => some .eq
  | _ => none

/-- Extensional operation on every pair of Boolean values. Evaluation strategy
is not encoded in these relational operation graphs. -/
def BinaryHook.eval : BinaryHook → Bool → Bool → Bool
  | .and | .andThen => fun a b => a && b
  | .or | .orElse => fun a b => a || b
  | .xor | .ne => fun a b => a != b
  | .implies => fun a b => !a || b
  | .eq => fun a b => a == b

structure SortMetadata where
  origin : Kore.Modules.Origin
  name : String
  hasDomainValues : Bool
  deriving DecidableEq, Repr

structure Source where
  definition : Aliases.SourceDefinition
  sorts : List SortMetadata
  deriving Repr

namespace Syntax

/-- Only the exact Boolean sort hook and optional nullary hasDomainValues are
accepted. Duplicate, malformed and unknown attributes reject. -/
def sortWithMetadata (hooked : Bool) : Parser
    (Kore.Modules.Declaration RawPattern Aliases.Declaration × Bool) := fun ts => do
  if !hooked then do
    let (d, ts) ← Kore.Modules.Syntax.ordinarySort false ts
    return ((d, false), ts)
  else do
    let (name, ts) ← identifier ts
    let (_, ts) ← Kore.Modules.Syntax.emptyBraces ts
    let (_, ts) ← punct '[' ts
    let (_, ts) ← word "hook" ts
    let (_, ts) ← Kore.Modules.Syntax.emptyBraces ts
    let (_, ts) ← punct '(' ts
    let .literal "BOOL.Bool" :: ts := ts | none
    let (_, ts) ← punct ')' ts
    let (domainValues, ts) ← match ts with
      | .punctuation ',' :: ts => do
          let (_, ts) ← word "hasDomainValues" ts
          let (_, ts) ← Kore.Modules.Syntax.emptyBraces ts
          let (_, ts) ← punct '(' ts
          let (_, ts) ← punct ')' ts
          pure (true, ts)
      | ts => pure (false, ts)
    let (_, ts) ← punct ']' ts
    return ((.hookedSort name "BOOL.Bool", domainValues), ts)

def sortDeclaration (hooked : Bool) : Parser (Kore.Modules.Declaration RawPattern Aliases.Declaration) := fun ts => do
  let ((d, _), ts) ← sortWithMetadata hooked ts
  return (d, ts)

/-- Raw hook strings remain attached to their original named declarations. -/
def symbol (hooked : Bool) : Parser (Kore.Modules.Declaration RawPattern Aliases.Declaration) := fun ts => do
  let (d, ts) ← Kore.Modules.Syntax.profile ts
  if !hooked then do
    let (_, ts) ← Kore.Modules.Syntax.emptyAttributes ts
    return (.symbol d, ts)
  else do
    let (_, ts) ← punct '[' ts
    let (_, ts) ← word "hook" ts
    let (_, ts) ← Kore.Modules.Syntax.emptyBraces ts
    let (_, ts) ← punct '(' ts
    let .literal name :: ts := ts | none
    let (_, ts) ← punct ')' ts
    let (_, ts) ← punct ']' ts
    if name = "BOOL.not" || (BinaryHook.parse name).isSome then
      return (.hookedSymbol d name, ts)
    else none

/-- Re-read only the exact located sort declaration to retain its annotation.
The shared parser records original token offsets and lengths, before erasure. -/
def metadata (ts : List Token) (m : Aliases.SourceModule) : Option (List SortMetadata) :=
  m.declarations.zipIdx.filterMapM fun (item, i) => do
    match item.declaration with
    | .hookedSort name _ =>
        let slice := (ts.drop item.location.tokenOffset).take item.location.tokenLength
        let .name "hooked-sort" :: rest := slice | none
        let ((_, dv), rest) ← sortWithMetadata true rest
        if rest.isEmpty then return some ⟨⟨m.name, i⟩, name, dv⟩ else none
    | _ => pure none

def parse (text : String) : Option Source := do
  let ts ← FixedPoint.Syntax.lex (text.toList.length + 1) text.toList []
  let (_, rest) ← Kore.Modules.Syntax.emptyAttributes ts
  let readPattern := Builtins.Syntax.patternWith (fun _ _ => true)
  let ms ← Kore.Modules.Syntax.modulesWithAliasAndSorts readPattern
    (Builtins.Syntax.aliasDeclarationWith readPattern) symbol sortDeclaration
    ts.length (ts.length + 1) rest
  if ms.isEmpty then none else do
    let sorts ← ms.flatMapM (metadata ts)
    return ⟨⟨ms⟩, sorts⟩
end Syntax

/-- Select the declared Boolean carrier. The second binding is a fresh unused
semantic carrier index; no source sort or symbol is inserted. It permits reuse
of the existing Int/Bool literal adequacy theorem. Original visibility checks
still reject every occurrence of that undeclared index in a source pattern. -/
def resolve (source : Source) : Option Builtins.SortBindings := do
  let [boolean] := source.sorts | none
  let unused := Builtins.freshPrefix source.definition
  if distinct : unused ≠ boolean.name then
    some ⟨unused, boolean.name, distinct⟩
  else none

/-- Only declaration metadata is removed. Every original pattern, name, origin,
location, module order and alias body is preserved. BOOL.not uses its existing
law; binary Boolean hooks are constrained by the additional model laws below. -/
def erase (source : Source) : Aliases.SourceDefinition :=
  ⟨source.definition.modules.map fun m => {m with declarations := m.declarations.map fun item =>
    {item with declaration := match item.declaration with
      | .hookedSort name _ => .sort name
      | .hookedSymbol d name => if name = "BOOL.not" then .hookedSymbol d name else .symbol d
      | other => other}}⟩

structure HookBinding where
  symbol : Kore.Modules.NamedSymbol
  hook : BinaryHook
  deriving DecidableEq, Repr

/-- Bind each recognized original hook to its exact origin and require every
argument and result to be the selected declared Boolean sort. -/
def hooks (source : Source) (sort : String) : Option (List HookBinding) :=
  source.definition.modules.flatMapM fun m =>
    m.declarations.zipIdx.filterMapM fun (item, i) => do
      match item.declaration with
      | .hookedSymbol d name =>
          if name = "BOOL.not" then
            if d.arguments == [sort] && d.result == sort then pure none else none
          else do
            let hook ← BinaryHook.parse name
            if d.arguments == [sort, sort] && d.result == sort then
              return some ⟨⟨⟨m.name, i⟩, d⟩, hook⟩
            else none
      | _ => pure none
end Silmaril.Logic.Kore.GeneralFixedPoint.BooleanRuntime
