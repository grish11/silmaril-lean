module

public import Silmaril.Languages.Starlark.Functions.Arguments.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Builtins

open Lists
open Lists.Iteration (iterationSource truth)

def typeName : Lists.Value → String
  | .scalar .none => "NoneType"
  | .scalar (.bool _) => "bool"
  | .scalar (.int _) => "int"
  | .string _ => "string"
  | .list _ => "list"
  | .tuple _ => "tuple"
  | .dict _ => "dict"
  | .function _ => "function"
  | .builtin _ => "builtin_function_or_method"

def minArity : Builtin → Nat
  | .len | .type => 1
  | .bool | .list | .tuple => 0

def arityError (id : Builtin) (supplied : Nat) : Error :=
  .builtinArity id (minArity id) 1 supplied

/-- Read the same finite snapshot as a collection loop. This operation has
no user code or callbacks, so iterator acquisition and release are unobservable. -/
def items (id : Builtin) : Lists.Value → Meaning (List Lists.Value)
  | value@(.list _) | value@(.tuple _) | value@(.dict _) =>
    Prod.snd <$> iterationSource value
  | value => throw (.builtinType id value)

def countValue (count : Nat) : Lists.Value := .scalar (.int (Int.ofNat count))
def boolValue (value : Bool) : Lists.Value := .scalar (.bool value)

def unary : Builtin → Lists.Value → Meaning Lists.Value
  | .bool, value => boolValue <$> truth value
  | .len, .string text => pure (countValue text.utf8ByteSize)
  | .len, value => (countValue ∘ List.length) <$> items .len value
  | .type, value => pure (.string (typeName value))
  | .list, value => items .list value >>= allocate
  | .tuple, value => items .tuple value >>= allocateTuple

/-- Apply a universal built-in to expanded arguments. All five accept only
positional arguments, and keyword rejection precedes the other checks. -/
def invoke (id : Builtin) (actual : Actual) : Meaning Lists.Value :=
  match actual.keywords, actual.positional with
  | (name, _) :: _, _ => throw (.builtinKeyword id name)
  | [], [value] => unary id value
  | [], [] =>
    match id with
    | .bool => pure (boolValue false)
    | .list => allocate []
    | .tuple => allocateTuple []
    | .len | .type => throw (arityError id 0)
  | [], _ :: _ :: _ => throw (arityError id actual.positional.length)

end Silmaril.Languages.Starlark.Functions.Builtins
