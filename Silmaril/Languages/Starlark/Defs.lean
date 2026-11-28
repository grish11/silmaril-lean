module

public import Silmaril.Languages.Starlark.Binary64.Defs

/-!
# Scalar Starlark syntax and domain

The source AST is parameterized by read and assignment names so lexical
resolution can preserve its shape. See `docs/projects/starlark.md` for the
pinned dialect and the interpretation of these entry points.
-/

@[expose] public section

namespace Silmaril.Languages.Starlark

inductive UnaryOp where
  | positive | negative | not
  deriving DecidableEq, Repr

inductive BinaryOp where
  | add | sub | mul | floorDiv | mod
  | eq | ne | lt | le | gt | ge
  deriving DecidableEq, Repr

inductive LogicalOp where
  | and | or
  deriving DecidableEq, Repr

inductive Expr (ref : Type) where
  | int (value : Int)
  | read (name : ref)
  | unary (op : UnaryOp) (arg : Expr ref)
  | binary (op : BinaryOp) (left right : Expr ref)
  | logical (op : LogicalOp) (left right : Expr ref)
  | conditional (test yes no : Expr ref)

inductive Stmt (ref target : Type) where
  | pass
  | eval (expr : Expr ref)
  | assign (name : target) (rhs : Expr ref)
  | seq (first rest : Stmt ref target)
  | branch (test : Expr ref) (yes no : Stmt ref target)
  /-- A bare return has no expression. -/
  | ret (value : Option (Expr ref))

abbrev SourceExpr := Expr String
abbrev SourceStmt := Stmt String String

inductive Value where
  | none
  | bool (value : Bool)
  | int (value : Int)
  /-- A supplied binary64 encoding. Structural equality compares its bits. -/
  | float (bits : UInt64)
  deriving DecidableEq, Repr

def Value.truth : Value → Bool
  | .none => false
  | .bool b => b
  | .int n => n != 0
  | .float value => Binary64.truth value

def LogicalOp.runsRight (op : LogicalOp) (left : Value) : Bool :=
  match op with
  | .and => left.truth
  | .or => !left.truth

inductive Scope where
  | local | global
  deriving DecidableEq, Repr

structure Binding where
  scope : Scope
  name : String
  deriving DecidableEq, Repr

inductive Ref where
  | bound (binding : Binding)
  /-- The lexical resolution of one of the three scalar predeclared names. -/
  | predeclared (value : Value)
  deriving DecidableEq, Repr

abbrev ResolvedExpr := Expr Ref
abbrev ResolvedStmt := Stmt Ref Binding

inductive RuntimeError where
  | uninitialized (binding : Binding)
  | unaryType (op : UnaryOp)
  | binaryType (op : BinaryOp)
  | zeroDivisor (op : BinaryOp)
  deriving DecidableEq, Repr

abbrev Result := Except RuntimeError

def applyUnary : UnaryOp → Value → Result Value
  | .not, v => .ok (.bool (!v.truth))
  | .positive, .int n => .ok (.int n)
  | .negative, .int n => .ok (.int (-n))
  | op, _ => .error (.unaryType op)

/-- Numbers share one exact order. Booleans order only against Booleans. -/
def Value.orderedCompare : Value → Value → Option Ordering
  | .int lhs, .int rhs => some (compare lhs rhs)
  | .int lhs, .float rhs => some (Binary64.compareNumbers (.ofInt lhs) (Binary64.decode rhs))
  | .float lhs, .int rhs => some (Binary64.compareNumbers (Binary64.decode lhs) (.ofInt rhs))
  | .float lhs, .float rhs => some (Binary64.compareNumbers (Binary64.decode lhs) (Binary64.decode rhs))
  | .bool lhs, .bool rhs => some (compare lhs rhs)
  | _, _ => Option.none

def BinaryOp.isComparison : BinaryOp → Bool
  | .eq | .ne | .lt | .le | .gt | .ge => true
  | _ => false

/-- `None` supports equality only. Unordered different types compare unequal. -/
def Value.isNone : Value → Bool
  | .none => true
  | _ => false

def comparisonResult (op : BinaryOp) (lhs rhs : Value) (order : Option Ordering) : Result Value :=
  match op, order with
  | .eq, some order => .ok (.bool (order == .eq))
  | .ne, some order => .ok (.bool (order != .eq))
  | .eq, none => .ok (.bool (lhs.isNone && rhs.isNone))
  | .ne, none => .ok (.bool (!(lhs.isNone && rhs.isNone)))
  | .lt, some order => .ok (.bool (order == .lt))
  | .le, some order => .ok (.bool (order != .gt))
  | .gt, some order => .ok (.bool (order == .gt))
  | .ge, some order => .ok (.bool (order != .lt))
  | _, _ => .error (.binaryType op)

def applyBinary : BinaryOp → Value → Value → Result Value
  | op@(.eq), lhs, rhs | op@(.ne), lhs, rhs | op@(.lt), lhs, rhs
  | op@(.le), lhs, rhs | op@(.gt), lhs, rhs | op@(.ge), lhs, rhs =>
    comparisonResult op lhs rhs (lhs.orderedCompare rhs)
  | .add, .int lhs, .int rhs => .ok (.int (lhs + rhs))
  | .sub, .int lhs, .int rhs => .ok (.int (lhs - rhs))
  | .mul, .int lhs, .int rhs => .ok (.int (lhs * rhs))
  | .floorDiv, .int lhs, .int rhs =>
    if rhs = 0 then .error (.zeroDivisor .floorDiv) else .ok (.int (lhs.fdiv rhs))
  | .mod, .int lhs, .int rhs =>
    if rhs = 0 then .error (.zeroDivisor .mod) else .ok (.int (lhs.fmod rhs))
  | op, _, _ => .error (.binaryType op)

/-- Absent entries include declared bindings that have yet to receive a value. -/
abbrev Bindings := String → Option Value

structure Frame where
  locals : Bindings := fun _ => none
  globals : Bindings := fun _ => none

def Frame.read (frame : Frame) : Ref → Result Value
  | .predeclared value => .ok value
  | .bound binding =>
    let slots := match binding.scope with
      | .local => frame.locals
      | .global => frame.globals
    match slots binding.name with
    | some value => .ok value
    | none => .error (.uninitialized binding)

def Frame.write (frame : Frame) (binding : Binding) (value : Value) : Frame :=
  match binding.scope with
  | .local => { frame with
      locals := fun name => if name = binding.name then some value else frame.locals name }
  | .global => { frame with
      globals := fun name => if name = binding.name then some value else frame.globals name }

/-- A suite either falls through or returns a value, including explicit Starlark `None`. -/
structure Completion where
  frame : Frame
  returned : Option Value

end Silmaril.Languages.Starlark
