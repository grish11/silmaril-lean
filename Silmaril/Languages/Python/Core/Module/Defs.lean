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
  | none
  deriving DecidableEq, Repr

def Value.asInt? : Value → Option Int
  | .int value => some value
  | .bool false => some 0
  | .bool true => some 1
  | .none => Option.none

/-- Numeric equality compares the integer projections. The singleton
`None` is the only nonnumeric value in this profile. -/
def Value.equal : Value → Value → Bool
  | .none, .none => true
  | left, right =>
    match left.asInt?, right.asInt? with
    | some first, some second => decide (first = second)
    | _, _ => false

def Value.truth : Value → Bool
  | .int value => decide (value ≠ 0)
  | .bool value => value
  | .none => false

/-- Look up the newest equal entry in a checked dictionary display. -/
def dictionaryGet {Key Item : Type} (same : Key → Key → Bool)
    (entries : List (Key × Item)) (key : Key) (fallback : Item) : Item :=
  ((entries.reverse.find? fun entry => same entry.1 key).map Prod.snd).getD fallback

def scalarDictionaryGet (entries : List (Value × Value)) (key fallback : Value) : Value :=
  dictionaryGet Value.equal entries key fallback

/-- Exactly the singleton objects distinguished by the identity profile. -/
inductive Singleton where
  | none_
  | boolean (value : Bool)
  deriving DecidableEq

def Value.singleton? : Value → Option Singleton
  | .none => some .none_
  | .bool value => some (.boolean value)
  | .int _ => Option.none

inductive IdentityOperator where
  | is_ | isNot
  deriving Repr

def IdentityOperator.test (operator : IdentityOperator) (left right : Singleton) : Bool :=
  match operator with
  | .is_ => decide (left = right)
  | .isNot => decide (left ≠ right)

namespace Identity

theorem sizeOf_operand_lt {α : Type} [SizeOf α] {links : List (IdentityOperator × α)}
    {link : IdentityOperator × α} (member : link ∈ links) : sizeOf link.2 < sizeOf links := by
  have smaller := List.sizeOf_lt_of_mem member
  rcases link with ⟨operator, operand⟩
  simp at smaller ⊢
  omega

def project {α : Type} {ε : Type} (singleton : α → Option Singleton)
    (unsupported : ε) (read : Except ε α) : Except ε Singleton :=
  read.bind fun value =>
    match singleton value with
    | some exact => .ok exact
    | none => .error unsupported

/-- Evaluate a reached right operand once. Carry that singleton into the
next comparison on success. The suppliers after a false link stay unused. -/
def scan {ε : Type} (left : Singleton) :
    List (IdentityOperator × (Unit → Except ε Singleton)) → Except ε Bool
  | [] => .ok true
  | (operator, read) :: rest =>
    (read ()).bind fun right =>
      if operator.test left right then scan right rest else .ok false

inductive Scans {ε : Type} :
    Singleton → List (IdentityOperator × (Unit → Except ε Singleton)) → Except ε Bool → Prop where
  | done (left : Singleton) : Scans left [] (.ok true)
  | error {left operator read rest error} (failed : read () = .error error) :
      Scans left ((operator, read) :: rest) (.error error)
  | stop {left operator read right rest} (found : read () = .ok right)
      (different : operator.test left right = false) : Scans left ((operator, read) :: rest) (.ok false)
  | next {left operator read right rest result} (found : read () = .ok right)
      (passed : operator.test left right = true) (tail : Scans right rest result) :
      Scans left ((operator, read) :: rest) result

end Identity

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
  | unsupportedArithmetic
  | unsupportedIdentity
  deriving DecidableEq, Repr

abbrev Evaluated := Except Error Value

inductive Operator where
  | arithmetic (op : Core.BinOp)
  | equal
  | notEqual
  deriving DecidableEq, Repr

def Operator.eval : Operator → Value → Value → Evaluated
  | .arithmetic op, left, right => do
    let some first := left.asInt? | .error .unsupportedArithmetic
    let some second := right.asInt? | .error .unsupportedArithmetic
    ((op.eval first second).map .int).mapError .arithmetic
  | .equal, left, right => .ok (.bool (left.equal right))
  | .notEqual, left, right => .ok (.bool (!left.equal right))

inductive Operator.Eval : Operator → Value → Value → Evaluated → Prop where
  | arithmetic {op left right first second result} :
      left.asInt? = some first → right.asInt? = some second → op.Eval first second result →
      Eval (.arithmetic op) left right ((result.map .int).mapError .arithmetic)
  | unsupportedLeft {op left right} : left.asInt? = none →
      Eval (.arithmetic op) left right (.error .unsupportedArithmetic)
  | unsupportedRight {op left right first} : left.asInt? = some first → right.asInt? = none →
      Eval (.arithmetic op) left right (.error .unsupportedArithmetic)
  | equal {left right : Value} {same : Bool} (checked : left.equal right = same) :
      Eval .equal left right (.ok (.bool same))
  | notEqual {left right : Value} {same : Bool} (checked : left.equal right = same) :
      Eval .notEqual left right (.ok (.bool (!same)))

inductive Expr where
  | literal (value : Value)
  | readGlobal (name : GlobalName)
  | binary (op : Operator) (left right : Expr)
  | identityChain (left : Expr) (links : List (IdentityOperator × Expr))
  deriving Repr

def Expr.eval (globals : Globals) : Expr → Evaluated
  | .literal value => .ok value
  | .readGlobal name =>
    match globals.lookup name with
    | some value => .ok value
    | none => .error (.nameError name)
  | .binary op left right =>
    (left.eval globals).bind fun first => (right.eval globals).bind (op.eval first)
  | .identityChain left links =>
    (Identity.project Value.singleton? .unsupportedIdentity (left.eval globals)).bind fun first =>
      (Identity.scan first (links.attach.map fun link =>
        (link.val.1, fun _ => Identity.project Value.singleton? .unsupportedIdentity (link.val.2.eval globals)))).map .bool
termination_by expression => sizeOf expression
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | have smaller := Identity.sizeOf_operand_lt link.property
      omega

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

  | identityHeadError {left links value error} :
      Evals globals left value → Identity.project Value.singleton? .unsupportedIdentity value = .error error →
      Evals globals (.identityChain left links) (.error error)
  | identityChain {left links value first result} :
      Evals globals left (.ok value) → value.singleton? = some first →
      Identity.Scans first
        (links.map fun link =>
          (link.1, fun _ => Identity.project Value.singleton? .unsupportedIdentity (link.2.eval globals))) result →
      Evals globals (.identityChain left links) (result.map .bool)

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
