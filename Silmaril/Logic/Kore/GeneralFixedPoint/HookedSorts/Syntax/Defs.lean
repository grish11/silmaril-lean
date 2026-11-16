module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Modules.Defs

/-! Monomorphic hooked sorts. Reading retains the exact source metadata;
resolution selects one declared integer sort and one distinct Boolean sort.
Literal texts and symbol profiles are checked only after this resolution. -/
@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.HookedSorts
open Operational.Text
open Builtins

inductive SortHook where
  | integer
  | boolean
  deriving DecidableEq, Repr

def SortHook.parse : String → Option SortHook
  | "INT.Int" => some .integer
  | "BOOL.Bool" => some .boolean
  | _ => none

structure SortBinding where
  origin : Kore.Modules.Origin
  name : String
  hook : SortHook
  deriving DecidableEq, Repr

/-- Exact original module/declaration origins, including hooked sorts. -/
def sortBindings (source : Aliases.SourceDefinition) : Option (List SortBinding) :=
  source.modules.flatMapM fun m =>
    m.declarations.zipIdx.filterMapM fun (item, i) =>
      match item.declaration with
      | .hookedSort name hook => do
          return some ⟨⟨m.name, i⟩, name, ← SortHook.parse hook⟩
      | _ => pure none

/-- This profile requires exactly one declaration for each builtin sort hook.
No conventional source name is privileged and no unknown sort hook is ignored. -/
def resolve (source : Aliases.SourceDefinition) : Option Builtins.SortBindings := do
  let bindings ← sortBindings source
  let [integer] := bindings.filter (fun b => b.hook == .integer) | none
  let [boolean] := bindings.filter (fun b => b.hook == .boolean) | none
  if distinct : integer.name ≠ boolean.name then
    some ⟨integer.name, boolean.name, distinct⟩
  else none

/-- Only the metadata constructor is erased. Names, locations, order, imports,
aliases and all original raw patterns are retained without substitution. -/
def erase (source : Aliases.SourceDefinition) : Aliases.SourceDefinition :=
  ⟨source.modules.map fun m => {m with declarations := m.declarations.map fun item =>
    {item with declaration := match item.declaration with
      | .hookedSort name _ => .sort name
      | other => other}}⟩

namespace Syntax

def sortDeclaration : Bool → Parser (Kore.Modules.Declaration RawPattern Aliases.Declaration) :=
  Kore.Modules.Syntax.hookedSortWith (fun hook => (SortHook.parse hook).isSome)

/-- This reader does not guess builtin names before declarations are known.
The package checker validates every literal and hook profile after resolution. -/
def parse (text : String) : Option Aliases.SourceDefinition := do
  let ts ← FixedPoint.Syntax.lex (text.toList.length + 1) text.toList []
  let (_, rest) ← Kore.Modules.Syntax.emptyAttributes ts
  let readPattern := Builtins.Syntax.patternWith (fun _ _ => true)
  let ms ← Kore.Modules.Syntax.modulesWithAliasAndSorts readPattern
    (Builtins.Syntax.aliasDeclarationWith readPattern)
    (Builtins.Syntax.symbolWith (fun _ _ => true)) sortDeclaration
    ts.length (ts.length + 1) rest
  if ms.isEmpty then none else some ⟨ms⟩
end Syntax
end Silmaril.Logic.Kore.GeneralFixedPoint.HookedSorts
