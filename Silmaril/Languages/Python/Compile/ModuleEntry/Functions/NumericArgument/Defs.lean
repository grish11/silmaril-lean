module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Defs

/-! # Closed numeric arguments

Check complete positional argument expressions over exact integer literals.
Comparisons also accept Boolean literals as numeric operands and return an
exact Boolean. Successful checks produce the existing literal operand, so
the call still uses its live callable and its usual argument delivery.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument

open Source (BinaryOperator Expr)

inductive Result where
  | integer (value : Int)
  | boolean (value : Bool)

def Result.operand (result : Result) (scope : Source.Scope) : Operand scope :=
  match result with
  | .integer value => .integer value
  | .boolean value => .boolean value

def signBit : Int → Bool
  | .ofNat _ => false
  | .negSucc _ => true

def bitPayload : Int → Nat
  | .ofNat bits | .negSucc bits => bits

/-- A negative integer has the complemented bits of its predecessor payload. -/
def testBit (value : Int) (index : Nat) : Bool :=
  (bitPayload value).testBit index ^^ signBit value

/-- Apply a bit operation to the unbounded two's-complement representations.
Store the finite deviations from the result's sign bit in the payload. -/
def bitwise (operation : Bool → Bool → Bool) (left right : Int) : Int :=
  let lhs := signBit left
  let rhs := signBit right
  let sign := operation lhs rhs
  let bits := Nat.bitwise (fun x y => operation (x ^^ lhs) (y ^^ rhs) ^^ sign)
    (bitPayload left) (bitPayload right)
  if sign then .negSucc bits else .ofNat bits

def binary? (operator : BinaryOperator) (left right : Int) : Option Int :=
  match operator with
  | .bitAnd => some (bitwise (· && ·) left right)
  | .bitOr => some (bitwise (· || ·) left right)
  | .bitXor => some (bitwise (· ^^ ·) left right)
  | .shiftLeft =>
    -- Bound the compile-time growth of the literal. A right shift does not grow it.
    if 0 ≤ right && right ≤ 4096 then some (left <<< right.toNat) else none
  | .shiftRight => if 0 ≤ right then some (left >>> right.toNat) else none
  | _ => none

def integer? : Expr → Option Int
  | .integer value => some value
  | .unary .positive operand => integer? operand
  | .unary .negative operand => (integer? operand).map (fun value => -value)
  | .unary .invert operand => (integer? operand).map Int.not
  | .binary operator left right => do
    let lhs ← integer? left
    let rhs ← integer? right
    binary? operator lhs rhs
  | _ => none

def numeric? : Expr → Option Int
  | .boolean value => some (Int.ofNat value.toNat)
  | operand => integer? operand

def check : Expr → Option Result
  | .comparison left [(operator, right)] => do
    let test ← ScalarComparison.ofSource? operator
    let lhs ← numeric? left
    let rhs ← numeric? right
    return .boolean (test.test lhs rhs)
  | operand => (integer? operand).map .integer

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument
