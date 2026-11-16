module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Defs

set_option linter.concreteInstances false
@[expose] public section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
open Kore.Modules.Checking
variable [SortBindings]

/-- Resolve exactly the first declaration used by the independent interpreter,
then require the declared hook binding and its complete profile. -/
def hook? (scope : Modules.Scope) (hooks : List HookBinding) (name : String) : Option Hook := do
  let symbol ← scope.symbols.find? (fun d => d.declaration.name == name)
  let binding ← hooks.find? (fun b => b.symbol == symbol)
  if binding.hook.valid symbol.declaration then some binding.hook else none

def literalPattern : (s : ValueSort) → Literal → Option (Pattern s)
  | .integer, .integer n => some (.integer n)
  | .boolean, .boolean b => some (.boolean b)
  | _, _ => none

def hookPattern (child : (s : ValueSort) → RawPattern → Option (Pattern s)) :
    (s : ValueSort) → Hook → List RawPattern → Option (Pattern s)
  | .boolean, .intEq, [p, q] => do
    return .intEq (← child .integer p) (← child .integer q)
  | .boolean, .boolNot, [p] => do return .boolNot (← child .boolean p)
  | _, _, _ => none

/-- The accepted source language is explicit. In particular no ordinary symbol,
alias, binder, fixed point or set variable is silently reinterpreted. -/
def check (scope : Modules.Scope) (hooks : List HookBinding) :
    Nat → (s : ValueSort) → RawPattern → Option (Pattern s)
  | 0, _, _ => none
  | n + 1, s, raw => do
    if !namedSort scope s.name then none else
    match raw with
    | .evar name actual =>
      if actual = s.name then some (.variable s name) else none
    | .domainValue actual text =>
      if actual ≠ s.name then none else do
        let value ← Literal.parse actual text
        literalPattern s value
    | .top actual => if actual = s.name then some (.top s) else none
    | .bottom actual => if actual = s.name then some (.bottom s) else none
    | .neg actual p =>
      if actual = s.name then return .neg (← check scope hooks n s p) else none
    | .conj actual p q =>
      if actual = s.name then
        return .conj (← check scope hooks n s p) (← check scope hooks n s q)
      else none
    | .disj actual p q =>
      if actual = s.name then
        return .disj (← check scope hooks n s p) (← check scope hooks n s q)
      else none
    | .app name args =>
      let hook ← hook? scope hooks name
      hookPattern (check scope hooks n) s hook args
    | _ => none

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt
