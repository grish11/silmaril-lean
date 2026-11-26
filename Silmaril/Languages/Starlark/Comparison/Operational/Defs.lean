module

public import Silmaril.Languages.Starlark.Defs

public section

namespace Silmaril.Languages.Starlark

@[expose] def OrderableTogether : Value → Value → Prop
  | .int _, .int _ | .int _, .float _ | .float _, .int _ | .float _, .float _ | .bool _, .bool _ => True
  | _, _ => False

/-- Relational comparison of scalar values, with independent binary64 field and order premises. -/
inductive ScalarOrders : Value → Value → Option Ordering → Prop where
  | integers {a b : Int} {order : Ordering} : Binary64.Orders (.finite a) (.finite b) order →
      ScalarOrders (.int a) (.int b) (some order)
  | intFloat {a : Int} {b : UInt64} {right : Binary64.Number} {order : Ordering} :
      Binary64.Decodes b right → Binary64.Orders (.ofInt a) right order →
      ScalarOrders (.int a) (.float b) (some order)
  | floatInt {a : UInt64} {b : Int} {left : Binary64.Number} {order : Ordering} :
      Binary64.Decodes a left → Binary64.Orders left (.ofInt b) order →
      ScalarOrders (.float a) (.int b) (some order)
  | floats {a b : UInt64} {left right : Binary64.Number} {order : Ordering} :
      Binary64.Decodes a left → Binary64.Decodes b right → Binary64.Orders left right order →
      ScalarOrders (.float a) (.float b) (some order)
  | booleans (a b : Bool) : ScalarOrders (.bool a) (.bool b) (some (compare a b))
  | unavailable {lhs rhs : Value} : ¬ OrderableTogether lhs rhs → ScalarOrders lhs rhs none

/-- Read the derived order using the comparison operator's truth condition. -/
@[expose] def ComparisonAnswer (op : BinaryOp) (lhs rhs : Value) (order : Option Ordering)
    (out : Result Value) : Prop :=
  match op, order with
  | .eq, some order => .ok (.bool (decide (order = .eq))) = out
  | .ne, some order => .ok (.bool (decide (order = .lt ∨ order = .gt))) = out
  | .lt, some order => .ok (.bool (decide (order = .lt))) = out
  | .le, some order => .ok (.bool (decide (order = .lt ∨ order = .eq))) = out
  | .gt, some order => .ok (.bool (decide (order = .gt))) = out
  | .ge, some order => .ok (.bool (decide (order = .eq ∨ order = .gt))) = out
  | .eq, none => .ok (.bool (decide (lhs = .none ∧ rhs = .none))) = out
  | .ne, none => .ok (.bool (decide (lhs ≠ .none ∨ rhs ≠ .none))) = out
  | _, _ => .error (.binaryType op) = out

inductive Compares (op : BinaryOp) (lhs rhs : Value) : Result Value → Prop where
  | result {order : Option Ordering} {out : Result Value} :
      op.isComparison = true → ScalarOrders lhs rhs order → ComparisonAnswer op lhs rhs order out →
      Compares op lhs rhs out

end Silmaril.Languages.Starlark
