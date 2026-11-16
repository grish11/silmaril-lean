module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Syntax.Defs
public import Silmaril.Logic.Kore.GeneralFixedPoint.Checking.Defs

/-! Monomorphic general KORE aliases. Formal parameters retain their namespace
and source order; bodies use the full general μ/ν syntax. -/
@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Aliases

structure Formal where
  isSet : Bool
  name : String
  sort : String
  deriving DecidableEq, Repr

structure Declaration where
  symbol : Modules.SymbolDeclaration
  parameters : List Formal
  body : RawPattern
  deriving Repr

def Declaration.names (d : Declaration) (isSet : Bool) : Names :=
  d.parameters.filterMap fun p => if p.isSet == isSet then some (p.name, p.sort) else none

/-- Retrieve an actual by the identity of its formal. Declaration validation
requires distinct formal names within each namespace and the declared sorts. -/
def Declaration.argument (d : Declaration) (args : List RawPattern)
    (isSet : Bool) (name : String) : Option RawPattern := do
  let pair ← (d.parameters.zip args).find? fun p => p.1.isSet == isSet && p.1.name == name
  return pair.2

/-- This is syntax/sort validation, not a semantic preservation premise. Body
closure and result sorting are checked by elaboration in the fresh formals. -/
def Declaration.valid (scope : Modules.Scope) (d : Declaration) : Bool :=
  d.parameters.map Formal.sort == d.symbol.arguments &&
  (d.parameters.map fun p => (p.isSet, p.name)).eraseDups.length == d.parameters.length &&
  d.symbol.arguments.all (Modules.Checking.namedSort scope) &&
  Modules.Checking.namedSort scope d.symbol.result

namespace Syntax
open Operational.Text

def parameters (name : String) (p : RawPattern) : Option (List Formal) := do
  let .app actual args := p | none
  if actual ≠ name then none else
    args.mapM fun p => match p with
      | .evar n s => some ⟨false, n, s⟩
      | .svar n s => some ⟨true, n, s⟩
      | _ => none

/-- The alias sentence itself, including `alias`, `where` and attributes. -/
def declaration (fuel : Nat) : Parser Declaration := fun ts => do
  let (_, ts) ← word "alias" ts
  let (symbol, ts) ← Modules.Syntax.profile ts
  let (_, ts) ← word "where" ts
  let (lhs, ts) ← GeneralFixedPoint.Syntax.pattern fuel ts
  let ps ← parameters symbol.name lhs
  let (_, ts) ← punct ':' ts
  let (_, ts) ← punct '=' ts
  let (body, ts) ← GeneralFixedPoint.Syntax.pattern fuel ts
  let (_, ts) ← Modules.Syntax.emptyAttributes ts
  return (⟨symbol, ps, body⟩, ts)
end Syntax
end Silmaril.Logic.Kore.GeneralFixedPoint.Aliases
