module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.NumericArgument.Defs
public import Silmaril.Languages.Python.Core.Binary64.Defs
public import Silmaril.Numeric.Ieee754.Operations

/-! # Closed tests in module control flow

The evaluator keeps exact scalar tags and binary64 bits. Text compares by
code point. Literal dictionaries expose only their truth value, after
checking every key and value. The accepted test grammar has no name reads,
calls, or effects.
-/

@[expose] public section
namespace Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard

open Source (BinaryOperator BooleanOperator Comparison Expr Stmt UnaryOperator)
open Silmaril.Numeric.Ieee754 (F64)

inductive Value where
  | scalar (value : Core.Module.Value)
  | float (value : F64.Finite)
  | text (points : List UInt32)
  | dictionary (nonempty : Bool)

def Value.truth : Value → Bool
  | .scalar value => value.truth
  | .float value => !value.val.isZero
  | .text points => !points.isEmpty
  | .dictionary nonempty => nonempty

def validText (points : List UInt32) : Bool :=
  points.all fun point => point.toNat < 0x110000

def literal? : Expr → Option Value
  | .integer value => some (.scalar (.int value))
  | .boolean value => some (.scalar (.bool value))
  | .none_ => some (.scalar .none)
  | .floatBits bits => (F64.Finite.ofRaw? (F64.ofBits bits)).map .float
  | .floatDecimal coefficient exponent => (Core.Binary64.ofDecimal? false coefficient exponent).map .float
  | .text points => if validText points then some (.text points) else none
  | _ => none

def validEntry : Option Expr × Expr → Bool
  | (some (.text key), value) => validText key && (literal? value).isSome
  | _ => false

def unary? (operator : UnaryOperator) (value : Value) : Option Value :=
  match operator, value with
  | .not_, value => some (.scalar (.bool (!value.truth)))
  | .positive, .float value => some (.float value)
  | .negative, .float value => (F64.Finite.neg? value).map .float
  | .positive, .scalar value => value.asInt?.map fun int => .scalar (.int int)
  | .negative, .scalar value => value.asInt?.map fun int => .scalar (.int (-int))
  | .invert, .scalar (.int value) => some (.scalar (.int (Int.not value)))
  | _, _ => none

def binary? (operator : BinaryOperator) (left right : Value) : Option Value :=
  match operator, left, right with
  | .add, .float left, .float right => (F64.Finite.add? left right).map .float
  | .add, .scalar left, .scalar right => do
    let lhs ← left.asInt?
    let rhs ← right.asInt?
    return .scalar (.int (lhs + rhs))
  | operator, .scalar (.int left), .scalar (.int right) =>
    (NumericArgument.binary? operator left right).map fun value => .scalar (.int value)
  | _, _, _ => none

def testOrdering (operator : ScalarComparison) (order : Ordering) : Bool :=
  match operator with
  | .eq => order == .eq
  | .ne => order != .eq
  | .lt => order == .lt
  | .le => order != .gt
  | .gt => order == .gt
  | .ge => order != .lt

def testFloat (operator : ScalarComparison) (left right : F64) : Bool :=
  match operator with
  | .eq => left.equal right
  | .ne => !left.equal right
  | .lt => left.lessThan right
  | .le => left.lessEqual right
  | .gt => right.lessThan left
  | .ge => right.lessEqual left

def compare? (operator : Comparison) (left right : Value) : Option Bool :=
  match identityOperator? operator, left, right with
  | some identity, .scalar left, .scalar right => do
    let lhs ← left.singleton?
    let rhs ← right.singleton?
    return identity.test lhs rhs
  | some _, _, _ => none
  | none, .scalar left, .scalar right =>
    match operator with
    | .eq => some (left.equal right)
    | .ne => some (!left.equal right)
    | operator => do
      let test ← ScalarComparison.ofSource? operator
      let lhs ← left.asInt?
      let rhs ← right.asInt?
      return test.test lhs rhs
  | none, .float left, .float right => do
    let test ← ScalarComparison.ofSource? operator
    return testFloat test left.val right.val
  | none, .text left, .text right => do
    let test ← ScalarComparison.ofSource? operator
    return testOrdering test (compare left right)
  | none, _, _ => none

def continues (operator : BooleanOperator) (value : Value) : Bool :=
  match operator with
  | .and_ => value.truth
  | .or_ => !value.truth

/-- A connective selects an existing value, retaining its tag. -/
def select (operator : BooleanOperator) (first : Value) : List Value → Value
  | [] => first
  | next :: rest => if continues operator first then select operator next rest else first

inductive Selects (operator : BooleanOperator) : Value → List Value → Value → Prop where
  | last (value : Value) : Selects operator value [] value
  | stop {value next rest} (decided : continues operator value = false) :
      Selects operator value (next :: rest) value
  | next {value next rest result} (continued : continues operator value = true)
      (tail : Selects operator next rest result) : Selects operator value (next :: rest) result

/-- Check every link even if a false result will stop the scan. A right
operand is prepared once and reused as the left operand of its successor. -/
def checkedLinks (left : Value) : List (Comparison × Value) → Option (List Bool)
  | [] => some []
  | (operator, right) :: rest => do
    let result ← compare? operator left right
    let tail ← checkedLinks right rest
    return result :: tail

inductive ChecksLinks : Value → List (Comparison × Value) → List Bool → Prop where
  | done (left : Value) : ChecksLinks left [] []
  | next {left operator right rest result tail} (link : compare? operator left right = some result)
      (following : ChecksLinks right rest tail) :
      ChecksLinks left ((operator, right) :: rest) (result :: tail)

def evaluate : Expr → Option Value
  | .unary operator source => do
    let operand ← evaluate source
    unary? operator operand
  | .binary operator left right => do
    let lhs ← evaluate left
    let rhs ← evaluate right
    binary? operator lhs rhs
  | .booleanOp operator (first :: second :: rest) => do
    let value ← evaluate first
    let values ← (second :: rest).attach.mapM fun operand => evaluate operand.val
    return select operator value values
  | .comparison left (first :: rest) => do
    let value ← evaluate left
    let rights ← (first :: rest).attach.mapM fun link => do
      let right ← evaluate link.val.2
      return (link.val.1, right)
    let links ← checkedLinks value rights
    return .scalar (.bool (links.all id))
  | .dictionary entries =>
    if entries.all validEntry then some (.dictionary (!entries.isEmpty)) else none
  | source => literal? source
termination_by source => sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have smaller := List.sizeOf_lt_of_mem operand.property
      simp only [List.cons.sizeOf_spec] at smaller
      omega
    | have smaller := List.sizeOf_lt_of_mem link.property
      have right : sizeOf link.val.2 < sizeOf link.val := by cases link.val; simp
      simp only [List.cons.sizeOf_spec] at smaller
      omega

def isPass : Stmt → Bool
  | .pass => true
  | _ => false

/-- Dead arms are binder-free. Check the complete supported raise syntax
without resolving or invoking the named exception. -/
def skippedStatement : Stmt → Bool
  | .pass | .raise_ none none | .raise_ (some (.name _)) none => true
  | .raise_ (some (.call (.name _) [.text points])) none
  | .raise_ (some (.callWith (.name _) [(.positional, .text points)])) none => validText points
  | _ => false

inductive Omitted : Stmt → Value → Prop where
  | conditional {condition yes no value}
      (guard : evaluate condition = some value) (body : yes.isEmpty = false)
      (selected : (if value.truth then yes else no).all isPass = true)
      (skipped : (if value.truth then no else yes).all skippedStatement = true)
      (exceptional : (yes.all literalArmStatement && no.all literalArmStatement) = false) :
      Omitted (.if_ condition yes no) value

def omitted? : (statement : Stmt) → Option {value // Omitted statement value}
  | .if_ condition yes no =>
    if exceptional : (yes.all literalArmStatement && no.all literalArmStatement) = false then
      match guard : evaluate condition with
      | none => none
      | some value =>
        if body : yes.isEmpty = false then
          if selected : (if value.truth then yes else no).all isPass = true then
            if skipped : (if value.truth then no else yes).all skippedStatement = true then
              some ⟨value, .conditional guard body selected skipped exceptional⟩
            else none
          else none
        else none
    else none
  | _ => none

end Silmaril.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard
