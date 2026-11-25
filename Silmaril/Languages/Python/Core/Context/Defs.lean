module

public import Silmaril.Languages.Python.Core.Defs

/-! # Evaluation contexts for closed Python arithmetic -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Context

/-- A right-operand frame remembers an already evaluated integer. -/
inductive Frame where
  | left (op : BinOp) (right : Expr)
  | right (op : BinOp) (left : Int)
  deriving DecidableEq, Repr

def Frame.plug (frame : Frame) (hole : Expr) : Expr :=
  match frame with
  | .left op rhs => .binary op hole rhs
  | .right op lhs => .binary op (.int lhs) hole

/-- Frames are ordered from the root of the source expression to its focus. -/
def plug : List Frame → Expr → Expr
  | [], hole => hole
  | frame :: rest, hole => frame.plug (plug rest hole)

/-- An exception escapes every pending arithmetic context in this slice. -/
def resume (frames : List Frame) (next : Except Exception Expr) : Except Exception Expr :=
  next.map (plug frames)

structure Redex where
  op : BinOp
  left : Int
  right : Int
  deriving DecidableEq, Repr

def Redex.expr (redex : Redex) : Expr :=
  .binary redex.op (.int redex.left) (.int redex.right)

def Redex.contract (redex : Redex) : Except Exception Expr :=
  (redex.op.eval redex.left redex.right).map .int

inductive View where
  | value (value : Int)
  | redex (frames : List Frame) (focus : Redex)
  deriving DecidableEq, Repr

def View.expr : View → Expr
  | .value n => .int n
  | .redex frames r => plug frames r.expr

/-- Select the leftmost pending arithmetic operation after evaluating its operands. -/
def focus : Expr → View
  | .int value => .value value
  | .binary op left right =>
    match focus left with
    | .redex frames redex => .redex (.left op right :: frames) redex
    | .value a =>
      match focus right with
      | .redex frames redex => .redex (.right op a :: frames) redex
      | .value b => .redex [] ⟨op, a, b⟩

/-- Decompose, use the relational primitive, and replug a successful result. -/
def Reduces (source : Expr) (next : Except Exception Expr) : Prop :=
  ∃ (frames : List Frame) (redex : Redex) (result : Completion),
    plug frames redex.expr = source ∧ redex.op.Eval redex.left redex.right result ∧
      next = resume frames (result.map .int)

def reduce (expr : Expr) : Option (Except Exception Expr) :=
  match focus expr with
  | .value _ => none
  | .redex frames redex => some (resume frames redex.contract)

/-- Advance through the context selector with the existing Core labels and state type. -/
def advance (state : State) : Option (Option Completion × State) :=
  match state with
  | .returning expr@(.binary ..) => (reduce expr).map fun next => (none, State.resume next)
  | _ => state.advance

end Silmaril.Languages.Python.Core.Context
