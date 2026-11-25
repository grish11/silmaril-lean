module

public import Silmaril.Languages.Python.Core.Defs

/-! # Initialized, straight-line Python module execution -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Module

open Semantics.Operational

/-- Lowering supplies the normalized spelling selected by source resolution. -/
abbrev GlobalName := String

inductive Value where
  | int (value : Int)
  | bool (value : Bool)
  deriving DecidableEq, Repr

def Value.asInt : Value → Int
  | .int value => value
  | .bool false => 0
  | .bool true => 1

def Value.truth : Value → Bool
  | .int value => decide (value ≠ 0)
  | .bool value => value

/-- The initial namespace is supplied by the caller. Reads have no implicit
builtin or import fallback. -/
structure Globals where
  lookup : GlobalName → Option Value

def Globals.empty : Globals := ⟨fun _ => none⟩

def Globals.bind (globals : Globals) (name : GlobalName) (value : Value) : Globals :=
  ⟨fun query => if query = name then some value else globals.lookup query⟩

/-- Seed the namespace in order. The last occurrence of a name wins. -/
def Globals.ofBindings (bindings : List (GlobalName × Value)) : Globals :=
  bindings.foldl (fun globals (name, value) => globals.bind name value) Globals.empty

inductive Error where
  | nameError (name : GlobalName)
  | assertionError
  | arithmetic (error : Core.Exception)
  deriving DecidableEq, Repr

abbrev Evaluated := Except Error Value

inductive Operator where
  | arithmetic (op : Core.BinOp)
  | equal
  deriving DecidableEq, Repr

def Operator.eval : Operator → Value → Value → Evaluated
  | .arithmetic op, left, right =>
    ((op.eval left.asInt right.asInt).map .int).mapError .arithmetic
  | .equal, left, right => .ok (.bool (decide (left.asInt = right.asInt)))

inductive Operator.Eval : Operator → Value → Value → Evaluated → Prop where
  | arithmetic {op left right result} :
      op.Eval left.asInt right.asInt result →
      Eval (.arithmetic op) left right ((result.map .int).mapError .arithmetic)
  | equal {left right : Value} (same : left.asInt = right.asInt) :
      Eval .equal left right (.ok (.bool true))
  | unequal {left right : Value} (different : left.asInt ≠ right.asInt) :
      Eval .equal left right (.ok (.bool false))

inductive Expr where
  | literal (value : Value)
  | readGlobal (name : GlobalName)
  | binary (op : Operator) (left right : Expr)
  deriving Repr

def Expr.eval (globals : Globals) : Expr → Evaluated
  | .literal value => .ok value
  | .readGlobal name =>
    match globals.lookup name with
    | some value => .ok value
    | none => .error (.nameError name)
  | .binary op left right =>
    (left.eval globals).bind fun first => (right.eval globals).bind (op.eval first)

inductive Expr.Evals (globals : Globals) : Expr → Evaluated → Prop where
  | literal (value : Value) : Evals globals (.literal value) (.ok value)
  | found {name value} : globals.lookup name = some value → Evals globals (.readGlobal name) (.ok value)
  | missing {name} : globals.lookup name = none → Evals globals (.readGlobal name) (.error (.nameError name))
  | leftError {op left right error} : Evals globals left (.error error) →
      Evals globals (.binary op left right) (.error error)
  | rightError {op left right first error} : Evals globals left (.ok first) →
      Evals globals right (.error error) → Evals globals (.binary op left right) (.error error)
  | binary {op left right first second result} : Evals globals left (.ok first) →
      Evals globals right (.ok second) → op.Eval first second result → Evals globals (.binary op left right) result

inductive Stmt where
  | assignGlobal (name : GlobalName) (value : Expr)
  | assert (condition : Expr)
  deriving Repr

inductive Completion where
  | normal
  | raised (error : Error)
  deriving DecidableEq, Repr

structure Observation where
  completion : Completion
  globals : Globals

structure Entry where
  globals : Globals
  body : List Stmt

inductive State where
  | running (globals : Globals) (body : List Stmt)
  | finished (observation : Observation)

def Entry.start (entry : Entry) : State := .running entry.globals entry.body

inductive Label where
  | bindGlobal (name : GlobalName) (value : Value)
  | complete (result : Completion)
  deriving DecidableEq, Repr

abbrev Transition := Option Label × State

def State.complete (globals : Globals) (completion : Completion) : Transition :=
  (some (.complete completion), .finished ⟨completion, globals⟩)

/-- Successful assignments publish the binding. Successful assertions are
silent. An exception stops the body with its current namespace. -/
inductive Step : State → Option Label → State → Prop where
  | empty (globals : Globals) :
      Step (.running globals []) (some (.complete .normal)) (.finished ⟨.normal, globals⟩)
  | assign {globals name value result rest} : value.Evals globals (.ok result) →
      Step (.running globals (.assignGlobal name value :: rest)) (some (.bindGlobal name result))
        (.running (globals.bind name result) rest)
  | assignError {globals name value error rest} : value.Evals globals (.error error) →
      Step (.running globals (.assignGlobal name value :: rest)) (some (.complete (.raised error)))
        (.finished ⟨.raised error, globals⟩)
  | assertTrue {globals condition value rest} : condition.Evals globals (.ok value) → value.truth = true →
      Step (.running globals (.assert condition :: rest)) none (.running globals rest)
  | assertFalse {globals condition value rest} : condition.Evals globals (.ok value) → value.truth = false →
      Step (.running globals (.assert condition :: rest)) (some (.complete (.raised .assertionError)))
        (.finished ⟨.raised .assertionError, globals⟩)
  | assertError {globals condition error rest} : condition.Evals globals (.error error) →
      Step (.running globals (.assert condition :: rest)) (some (.complete (.raised error)))
        (.finished ⟨.raised error, globals⟩)

def State.advance : State → Option Transition
  | .finished _ => none
  | .running globals [] => some (State.complete globals .normal)
  | .running globals (.assignGlobal name expression :: rest) => some <|
    match expression.eval globals with
    | .ok value => (some (.bindGlobal name value), .running (globals.bind name value) rest)
    | .error error => State.complete globals (.raised error)
  | .running globals (.assert expression :: rest) => some <|
    match expression.eval globals with
    | .ok value =>
      if value.truth then (none, .running globals rest)
      else State.complete globals (.raised .assertionError)
    | .error error => State.complete globals (.raised error)

def State.budget : State → Nat
  | .running _ body => body.length + 1
  | .finished _ => 0

def observes : State → Outcome Observation → Prop
  | .finished observation, outcome => outcome = .returned observation
  | .running .., _ => False

def labelled : Labelled State Label Observation := ⟨Step, observes⟩

def semantics : WithUB State Observation :=
  WithUB.ofOpSem ⟨fun source target => ∃ label, Step source label target, observes⟩

def model : HasOpSem Entry State Observation :=
  ⟨fun entry state => state = entry.start, semantics⟩

/-- Follow at most the requested number of steps, retaining labels and the
residual state. A running residual is a prefix. -/
def runPrefix : Nat → State → List Label × State
  | 0, state => ([], state)
  | fuel + 1, state =>
    match state.advance with
    | none => ([], state)
    | some (label, target) =>
      let (log, residual) := runPrefix fuel target
      (label.toList ++ log, residual)

def Entry.run (entry : Entry) : List Label × State :=
  runPrefix entry.start.budget entry.start

end Silmaril.Languages.Python.Core.Module
