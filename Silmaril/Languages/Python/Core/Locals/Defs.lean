module

public import Silmaril.Languages.Python.Core.Context.Defs

/-! # A single Python frame with integer local slots -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Locals

open Semantics.Operational

variable {slots : Nat}

/-- An allocated slot is either unbound or holds an exact integer. -/
abbrev Store (slots : Nat) := Fin slots → Option Int

def Store.empty (slots : Nat) : Store slots := fun _ => none

def Store.write (store : Store slots) (slot : Fin slots) (value : Int) : Store slots :=
  fun index => if index = slot then some value else store index

inductive Error (slots : Nat) where
  | arithmetic (error : Exception)
  | unboundLocal (slot : Fin slots)
  deriving DecidableEq, Repr

abbrev Result (slots : Nat) := Except (Error slots) Int

inductive LogicalOp where
  | and
  | or
  deriving DecidableEq, Repr

def LogicalOp.runsRight : LogicalOp → Int → Bool
  | .and, value => value != 0
  | .or, value => value == 0

/-- An operand may be a closed arithmetic expression, a local read, or a compound expression. -/
inductive Rhs (slots : Nat) where
  | arithmetic (expr : Expr)
  | read (slot : Fin slots)
  | binary (op : BinOp) (left right : Rhs slots)
  | logical (op : LogicalOp) (left right : Rhs slots)
  deriving DecidableEq, Repr

def Rhs.lift (next : Except Exception Expr) : Except (Error slots) (Rhs slots) :=
  match next with
  | .ok expr => .ok (.arithmetic expr)
  | .error error => .error (.arithmetic error)

def Rhs.load (store : Store slots) (slot : Fin slots) : Result slots :=
  match store slot with
  | some value => .ok value
  | none => .error (.unboundLocal slot)

inductive Rhs.Step (store : Store slots) : Rhs slots → Except (Error slots) (Rhs slots) → Prop where
  | arithmetic {expr : Expr} {next : Except Exception Expr} :
      expr.Step next → Step store (.arithmetic expr) (lift next)
  | load (slot : Fin slots) (value : Int) :
      store slot = some value → Step store (.read slot) (.ok (.arithmetic (.int value)))
  | unbound (slot : Fin slots) :
      store slot = none → Step store (.read slot) (.error (.unboundLocal slot))

  | left {op : BinOp} {left right : Rhs slots} {next : Except (Error slots) (Rhs slots)} :
      Step store left next → Step store (.binary op left right) (next.map fun rhs => .binary op rhs right)
  | right {op : BinOp} {left : Int} {right : Rhs slots} {next : Except (Error slots) (Rhs slots)} :
      Step store right next →
        Step store (.binary op (.arithmetic (.int left)) right)
          (next.map (Rhs.binary op (.arithmetic (.int left))))
  | compute {op : BinOp} {left right : Int} {result : Completion} :
      op.Eval left right result →
        Step store (.binary op (.arithmetic (.int left)) (.arithmetic (.int right))) (lift (result.map .int))
  | logicalTest {op : LogicalOp} {left right : Rhs slots} {next : Except (Error slots) (Rhs slots)} :
      Step store left next → Step store (.logical op left right) (next.map fun rhs => .logical op rhs right)
  | logicalShort {op : LogicalOp} {left : Int} {right : Rhs slots} :
      op.runsRight left = false →
        Step store (.logical op (.arithmetic (.int left)) right) (.ok (.arithmetic (.int left)))
  | logicalRight {op : LogicalOp} {left : Int} {right : Rhs slots} :
      op.runsRight left = true → Step store (.logical op (.arithmetic (.int left)) right) (.ok right)

def Rhs.literal? : Rhs slots → Option Int
  | .arithmetic (.int value) => some value
  | _ => none

def Rhs.reduce (store : Store slots) : Rhs slots → Option (Except (Error slots) (Rhs slots))
  | .arithmetic expr => (Context.reduce expr).map lift
  | .read slot => some ((load store slot).map fun value => .arithmetic (.int value))
  | .binary op left right =>
    match left.literal? with
    | none => (reduce store left).map (·.map fun rhs => .binary op rhs right)
    | some a =>
      match right.literal? with
      | none => (reduce store right).map (·.map (Rhs.binary op (.arithmetic (.int a))))
      | some b => some (lift ((op.eval a b).map .int))
  | .logical op left right =>
    match left.literal? with
    | none => (reduce store left).map (·.map fun rhs => .logical op rhs right)
    | some value =>
      some (.ok (if op.runsRight value then right else .arithmetic (.int value)))

/-- A lowered function body ends in a return on each control-flow branch. -/
inductive Code (slots : Nat) where
  | ret (rhs : Rhs slots)
  | assign (slot : Fin slots) (rhs : Rhs slots) (rest : Code slots)
  | branch (test : Rhs slots) (yes no : Code slots)

inductive Continuation (slots : Nat) where
  | ret
  | assign (slot : Fin slots) (rest : Code slots)
  | branch (yes no : Code slots)

inductive State (slots : Nat) where
  | evaluating (store : Store slots) (rhs : Rhs slots) (cont : Continuation slots)
  | raising (store : Store slots) (error : Error slots)
  | finished (store : Store slots) (result : Result slots)

/-- Writes are frame instrumentation. Only exit results are language observations. -/
inductive Event (slots : Nat) where
  | write (slot : Fin slots) (value : Int)
  | exit (result : Result slots)

def State.enter (store : Store slots) : Code slots → State slots
  | .ret rhs => .evaluating store rhs .ret
  | .assign slot rhs rest => .evaluating store rhs (.assign slot rest)
  | .branch test yes no => .evaluating store test (.branch yes no)

def State.resume (store : Store slots) (cont : Continuation slots) :
    Except (Error slots) (Rhs slots) → State slots
  | .ok rhs => .evaluating store rhs cont
  | .error error => .raising store error

inductive Step : State slots → Option (Event slots) → State slots → Prop where
  | expression {store : Store slots} {rhs : Rhs slots} {cont : Continuation slots}
      {next : Except (Error slots) (Rhs slots)} :
      rhs.Step store next → Step (.evaluating store rhs cont) none (State.resume store cont next)
  | assign (store : Store slots) (slot : Fin slots) (value : Int) (rest : Code slots) :
      Step (.evaluating store (.arithmetic (.int value)) (.assign slot rest))
        (some (.write slot value)) (State.enter (store.write slot value) rest)
  | takeYes (store : Store slots) (value : Int) (yes no : Code slots) (nonzero : value ≠ 0) :
      Step (.evaluating store (.arithmetic (.int value)) (.branch yes no))
        none (State.enter store yes)
  | takeNo (store : Store slots) (yes no : Code slots) :
      Step (.evaluating store (.arithmetic (.int 0)) (.branch yes no))
        none (State.enter store no)
  | ret (store : Store slots) (value : Int) :
      Step (.evaluating store (.arithmetic (.int value)) .ret)
        (some (.exit (.ok value))) (.finished store (.ok value))
  | raise (store : Store slots) (error : Error slots) :
      Step (.raising store error) (some (.exit (.error error))) (.finished store (.error error))

inductive Observes : State slots → Outcome (Result slots) → Prop where
  | finished (store : Store slots) (result : Result slots) :
      Observes (.finished store result) (.returned result)

def labelled (slots : Nat) : Labelled (State slots) (Event slots) (Result slots) where
  step := Step
  observe := Observes

def ordinary (slots : Nat) : OpSem (State slots) (Result slots) where
  step source target := ∃ label, Step source label target
  observe := Observes

def model (slots : Nat) : HasOpSem (Code slots) (State slots) (Result slots) where
  initial code state := state = State.enter (Store.empty slots) code
  semantics := .ofOpSem (ordinary slots)

def State.advance : State slots → Option (Option (Event slots) × State slots)
  | .evaluating store (.arithmetic (.int value)) cont =>
    match cont with
    | .ret => some (some (.exit (.ok value)), .finished store (.ok value))
    | .assign slot rest => some (some (.write slot value), State.enter (store.write slot value) rest)
    | .branch yes no => some (none, State.enter store (if value = 0 then no else yes))
  | .evaluating store rhs cont =>
    (rhs.reduce store).map fun next => (none, State.resume store cont next)
  | .raising store error => some (some (.exit (.error error)), .finished store (.error error))
  | .finished _ _ => none

def State.pick (state : State slots) : Decision (State slots) (Result slots) :=
  match state with
  | .finished _ result => .stop (.observed (.returned result))
  | _ => state.advance.elim (.stop .unknown) fun transition => .move transition.2

def Rhs.work : Rhs slots → Nat
  | .arithmetic expr => expr.work
  | .read _ => 1
  | .binary _ left right | .logical _ left right => left.work + right.work + 1

def Code.budget : Code slots → Nat
  | .ret rhs => rhs.work + 2
  | .assign _ rhs rest => rhs.work + (rest.budget + 1)
  | .branch test yes no => test.work + (max yes.budget no.budget + 1)

def Continuation.budget : Continuation slots → Nat
  | .ret => 2
  | .assign _ rest => rest.budget + 1
  | .branch yes no => max yes.budget no.budget + 1

def State.budget : State slots → Nat
  | .evaluating _ rhs cont => rhs.work + cont.budget
  | .raising .. => 1
  | .finished .. => 0

structure Answer (slots : Nat) where
  store : Store slots
  result : Result slots

/-- A structural result specification that also retains the final local bindings. -/
def Rhs.eval (store : Store slots) : Rhs slots → Result slots
  | .arithmetic expr => expr.eval.mapError .arithmetic
  | .read slot => load store slot
  | .binary op left right =>
    (left.eval store).bind fun a => (right.eval store).bind fun b => (op.eval a b).mapError .arithmetic
  | .logical op left right =>
    (left.eval store).bind fun value => if op.runsRight value then right.eval store else .ok value

def Code.eval (store : Store slots) : Code slots → Answer slots
  | .ret rhs => ⟨store, rhs.eval store⟩
  | .assign slot rhs rest =>
    match rhs.eval store with
    | .ok value => rest.eval (store.write slot value)
    | .error error => ⟨store, .error error⟩
  | .branch test yes no =>
    match test.eval store with
    | .ok value => if value = 0 then no.eval store else yes.eval store
    | .error error => ⟨store, .error error⟩

def Continuation.finish (store : Store slots) (result : Result slots) : Continuation slots → Answer slots
  | .ret => ⟨store, result⟩
  | .assign slot rest =>
    match result with
    | .ok value => rest.eval (store.write slot value)
    | .error error => ⟨store, .error error⟩
  | .branch yes no =>
    match result with
    | .ok value => if value = 0 then no.eval store else yes.eval store
    | .error error => ⟨store, .error error⟩

def State.answer : State slots → Answer slots
  | .evaluating store rhs cont => cont.finish store (rhs.eval store)
  | .raising store error => ⟨store, .error error⟩
  | .finished store result => ⟨store, result⟩

end Silmaril.Languages.Python.Core.Locals
