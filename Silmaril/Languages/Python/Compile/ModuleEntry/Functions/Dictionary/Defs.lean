module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs
public import Silmaril.Languages.Python.Core.Module.Dictionary.Defs

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Dictionary

open Source (ArgumentKind Expr Scope)
open Core.Module.Dictionary (Atom Entry Get Clear Argument)

def atom? : Expr → Option Atom
  | .text points => (Core.Text.ofPoints? points).map .text
  | source => (exactScalarLiteral? source).map .scalar

def entry? : Option Expr × Expr → Option Entry
  | (some key, value) => do
    let checkedKey ← atom? key
    let checkedValue ← atom? value
    return (checkedKey, checkedValue)
  | (none, _) => none

def argument? (scope : Scope) : Expr → Option Argument
  | .name name => (globalReference? scope name).map fun _ => .global name
  | source => (atom? source).map .literal

/-- Check a named receiver with one or two positional arguments. Lookups
are deferred and the receiver's current value must supply the method. -/
def checkedGet? (scope : Scope) : Expr → Option Get
  | .call (.attribute (.name receiver) "get") arguments =>
    checkedArguments receiver (arguments.map (.positional, ·))
  | .callWith (.attribute (.name receiver) "get") arguments =>
    checkedArguments receiver arguments
  | _ => none
where
  checkedArguments (receiver : String) (arguments : List (ArgumentKind × Expr)) : Option Get := do
    let _ ← globalReference? scope receiver
    let (key, fallback) ← match arguments with
      | [(.positional, key)] => some (key, .none_)
      | [(.positional, key), (.positional, fallback)] => some (key, fallback)
      | _ => none
    let checkedKey ← argument? scope key
    let checkedFallback ← argument? scope fallback
    return ⟨receiver, checkedKey, checkedFallback⟩

/-- Admit the direct call only. Flat excess positional arguments reach the
stock arity error after their ordered preparation. -/
def checkedClear? (scope : Scope) : Expr → Option Clear
  | .call (.attribute (.name receiver) "clear") arguments =>
    checkedArguments receiver (arguments.map (.positional, ·))
  | .callWith (.attribute (.name receiver) "clear") arguments =>
    checkedArguments receiver arguments
  | _ => none
where
  checkedArguments (receiver : String) (arguments : List (ArgumentKind × Expr)) : Option Clear := do
    let _ ← globalReference? scope receiver
    let values ← arguments.mapM fun
      | (.positional, source) => argument? scope source
      | _ => none
    return ⟨receiver, values⟩

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Dictionary
