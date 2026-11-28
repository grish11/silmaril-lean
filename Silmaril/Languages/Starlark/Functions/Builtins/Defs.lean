module

public import Silmaril.Languages.Starlark.Functions.Arguments.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Functions.Builtins

open Lists
open Lists.Iteration (Cursor acquireIterator iterationSource truth)

def typeName : Lists.Value → String
  | .scalar .none => "NoneType"
  | .scalar (.bool _) => "bool"
  | .scalar (.int _) => "int"
  | .scalar (.float _) => "float"
  | .string _ => "string"
  | .range _ => "range"
  | .list _ => "list"
  | .tuple _ => "tuple"
  | .dict _ => "dict"
  | .function _ => "function"
  | .builtin _ => "builtin_function_or_method"

def minArity : Builtin → Nat
  | .len | .type | .range | .abs | .any | .all => 1
  | .bool | .list | .tuple => 0

def arityError (id : Builtin) (supplied : Nat) : Error :=
  .builtinArity id (minArity id) (if id = .range then 3 else 1) supplied

def rangeInteger : Lists.Value → Except Error Int
  | .scalar (.int i) => .ok i
  | value => .error (.builtinType .range value)

/-- Check the normalized constructor operands in positional order. -/
def checkedRange (start stop step : Lists.Value) : Except Error Lists.Value := do
  let first ← rangeInteger start
  let last ← rangeInteger stop
  let stride ← rangeInteger step
  if h : stride = 0 then throw .zeroRangeStep
  else pure (.range ⟨first, last, stride, h⟩)

def rangeArgs : List Lists.Value → Except Error Lists.Value
  | [stop] => checkedRange (.scalar (.int 0)) stop (.scalar (.int 1))
  | [start, stop] => checkedRange start stop (.scalar (.int 1))
  | [start, stop, step] => checkedRange start stop step
  | args => .error (arityError .range args.length)

/-- Read a collection snapshot or collect a range cursor in order. This
operation runs no Starlark code and leaves iterator guards alone. -/
def items (id : Builtin) : Lists.Value → Meaning (List Lists.Value)
  | value@(.list _) | value@(.tuple _) | value@(.dict _) =>
    Prod.snd <$> iterationSource value
  | .range span => pure (Cursor.ofRange span).collect
  | value => throw (.builtinType id value)

def countValue (count : Nat) : Lists.Value := .scalar (.int (Int.ofNat count))
def boolValue (value : Bool) : Lists.Value := .scalar (.bool value)

def absValue : Lists.Value → Meaning Lists.Value
  | .scalar (.int value) => pure (countValue value.natAbs)
  | .scalar (.float value) => pure (.scalar (.float (Binary64.abs value)))
  | value => throw (.builtinType .abs value)

/-- Test yielded values in order. A decisive truth value or an error ends the scan. -/
def truthCursor (stop : Bool) (cursor : Cursor) (state : State) : Outcome Lists.Value :=
  match _step : cursor.advance with
  | none => .ok (boolValue (!stop)) state
  | some (value, rest) =>
    Outcome.resume (truth value state) fun flag next =>
      if flag = stop then .ok (boolValue stop) next else truthCursor stop rest next
termination_by cursor.remaining
decreasing_by exact Cursor.advance_decreases _step

/-- The snapshot and truth reads run no user code, so no iterator guard needs to be installed. -/
def quantify (id : Builtin) (stop : Bool) (value : Lists.Value) (state : State) : Outcome Lists.Value :=
  match acquireIterator value state with
  | .error error next => .error (if error = .notIterable then .builtinType id value else error) next
  | .ok (_, cursor) next => truthCursor stop cursor next

def unary : Builtin → Lists.Value → Meaning Lists.Value
  | .bool, value => boolValue <$> truth value
  | .len, .string text => pure (countValue text.utf8ByteSize)
  | .len, .range span => pure (countValue span.length)
  | .len, value => (countValue ∘ List.length) <$> items .len value
  | .type, value => pure (.string (typeName value))
  | .list, value => items .list value >>= allocate
  | .tuple, value => items .tuple value >>= allocateTuple
  | .range, value => fromExcept (rangeArgs [value])
  | .abs, value => absValue value
  | .any, value => quantify .any true value
  | .all, value => quantify .all false value

/-- Apply a universal built-in to expanded arguments. All accept only
positional arguments, and keyword rejection precedes the other checks. -/
def invoke (id : Builtin) (actual : Actual) : Meaning Lists.Value :=
  match id, actual.keywords, actual.positional with
  | _, (name, _) :: _, _ => throw (.builtinKeyword id name)
  | _, [], [value] => unary id value
  | _, [], [] =>
    match id with
    | .bool => pure (boolValue false)
    | .list => allocate []
    | .tuple => allocateTuple []
    | .len | .type | .range | .abs | .any | .all => throw (arityError id 0)
  | .range, [], values@(_ :: _ :: _) => fromExcept (rangeArgs values)
  | _, [], _ :: _ :: _ => throw (arityError id actual.positional.length)

end Silmaril.Languages.Starlark.Functions.Builtins
