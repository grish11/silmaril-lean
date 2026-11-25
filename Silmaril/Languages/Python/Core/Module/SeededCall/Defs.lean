module

public import Silmaril.Languages.Python.Core.Closure.Defs

/-! # Closed callables for explicitly seeded module entry -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Module.SeededCall

open Core.Closure (RuntimeError)

inductive ExceptionClass where
  | assertionError
  | nameError
  | unboundLocalError
  | typeError
  | zeroDivisionError
  deriving DecidableEq, Repr

inductive AssertionArgument where
  | empty
  | text (message : String)
  | integerPair (left right : Int)
  deriving DecidableEq, Repr

inductive Raised where
  | assertionError (argument : AssertionArgument)
  | runtime (error : RuntimeError)
  deriving DecidableEq, Repr

def Raised.classify : Raised → ExceptionClass
  | .assertionError _ => .assertionError
  | .runtime (.unboundLocal _) | .runtime (.unboundOwned _) => .unboundLocalError
  | .runtime (.unboundCapture _) | .runtime (.nameError _) => .nameError
  | .runtime (.positionalArity ..) | .runtime .notCallable => .typeError
  | .runtime (.arithmetic .zeroDivisionError) => .zeroDivisionError

def ExceptionClass.catches (expected actual : ExceptionClass) : Prop :=
  expected = actual ∨ (expected = .nameError ∧ actual = .unboundLocalError)

instance (expected actual : ExceptionClass) : Decidable (expected.catches actual) := by
  unfold ExceptionClass.catches
  infer_instance

inductive Helper where
  | assertEqual
  | assertRaises (onReturn : AssertionArgument)
  deriving DecidableEq, Repr

inductive Value where
  | int (value : Int)
  | none
  | exceptionClass (kind : ExceptionClass)
  | helper (callable : Helper)
  deriving DecidableEq, Repr

inductive Failure where
  | raised (error : Raised)
  | unsupported
  deriving DecidableEq, Repr

abbrev Result := Except Failure Value
abbrev Bindings := List (String × Value)

def lookupBinding (bindings : Bindings) (name : String) : Option Value :=
  bindings.findSome? fun (key, value) => if name = key then some value else none

structure Namespace where
  moduleGlobals : Bindings
  builtins : Bindings

def Namespace.empty : Namespace := ⟨[], []⟩

/-- Global reads look in the module first. A present `None` is a binding. -/
def Namespace.lookupGlobal (space : Namespace) (name : String) : Option Value :=
  (lookupBinding space.moduleGlobals name).orElse (fun _ => lookupBinding space.builtins name)

def Namespace.bindGlobal (space : Namespace) (name : String) (value : Value) : Namespace :=
  { space with moduleGlobals := (name, value) :: space.moduleGlobals.filter (fun binding => binding.1 != name) }

/-- Lexical resolution makes the local/global choice before execution. -/
inductive Operand (slots : Nat) where
  | literal (value : Value)
  | local (slot : Fin slots)
  | global (name : String)
  | unsupported

abbrev Locals (slots : Nat) := Vector (Option Value) slots

def Operand.eval {slots : Nat} (space : Namespace) (locals : Locals slots) : Operand slots → Result
  | .literal value => .ok value
  | .local slot =>
    (locals.get slot).elim (.error (.raised (.runtime (.unboundLocal slot.val)))) .ok
  | .global name =>
    (space.lookupGlobal name).elim (.error (.raised (.runtime (.nameError name)))) .ok
  | .unsupported => .error .unsupported

structure Expectation where
  expected : ExceptionClass
  onReturn : AssertionArgument

def Expectation.deliver (expectation : Expectation) : Result → Result
  | .ok _ => .error (.raised (.assertionError expectation.onReturn))
  | .error (.raised error) =>
    if expectation.expected.catches error.classify then .ok .none else .error (.raised error)
  | .error .unsupported => .error .unsupported

inductive Delivers (expectation : Expectation) : Result → Result → Prop where
  | returned (value : Value) : Delivers expectation (.ok value)
      (.error (.raised (.assertionError expectation.onReturn)))
  | caught (error : Raised) (accepted : expectation.expected.catches error.classify) :
      Delivers expectation (.error (.raised error)) (.ok .none)
  | uncaught (error : Raised) (different : ¬ expectation.expected.catches error.classify) :
      Delivers expectation (.error (.raised error)) (.error (.raised error))
  | unsupported : Delivers expectation (.error .unsupported) (.error .unsupported)

/-- Decoding identifies the admitted typed call shapes. In particular,
calling an exception class would construct an object outside this profile. -/
inductive Request (arity : Nat) where
  | compare (left right : Int)
  | expect (expectation : Expectation) (callback : Value) (arguments : List Value)
      (shorter : arguments.length < arity)
  | nonCallable
  | unsupported

def Request.decode (callee : Value) (arguments : List Value) : Request arguments.length :=
  match callee, arguments with
  | .helper .assertEqual, [.int left, .int right] => .compare left right
  | .helper (.assertRaises onReturn), .exceptionClass expected :: callback :: arguments =>
    .expect ⟨expected, onReturn⟩ callback arguments (by simp only [List.length_cons]; omega)
  | .none, _ | .int _, _ => .nonCallable
  | _, _ => .unsupported

/-- Invoking an expectation calls the supplied closed callable using the
same dispatcher as a direct call. -/
def invoke (callee : Value) (arguments : List Value) : Result :=
  match Request.decode callee arguments with
  | .compare left right =>
    if left = right then .ok .none else .error (.raised (.assertionError (.integerPair left right)))
  | .expect expectation callback args _shorter =>
    expectation.deliver (invoke callback args)
  | .nonCallable => .error (.raised (.runtime .notCallable))
  | .unsupported => .error .unsupported
termination_by arguments.length

inductive Executes : {arity : Nat} → Request arity → Result → Prop where
  | equal {arity : Nat} (left right : Int) (same : left = right) :
      Executes (arity := arity) (.compare left right) (.ok .none)
  | unequal {arity : Nat} (left right : Int) (different : left ≠ right) :
      Executes (arity := arity) (.compare left right) (.error (.raised (.assertionError (.integerPair left right))))
  | expected {arity : Nat} {expectation : Expectation} {callback : Value} {arguments : List Value}
      {shorter : arguments.length < arity} {inner outer : Result} :
      Executes (Request.decode callback arguments) inner → Delivers expectation inner outer →
      Executes (.expect expectation callback arguments shorter) outer
  | nonCallable {arity : Nat} : Executes (arity := arity) .nonCallable (.error (.raised (.runtime .notCallable)))
  | unsupported {arity : Nat} : Executes (arity := arity) .unsupported (.error .unsupported)

def Operand.evalList {slots : Nat} (space : Namespace) (locals : Locals slots) :
    List (Operand slots) → Except Failure (List Value)
  | [] => .ok []
  | operand :: rest =>
    (operand.eval space locals).bind fun value => (evalList space locals rest).map (value :: ·)

/-- Resolve the callable, then resolve positional operands in order. Calls
and their supported callback do not write either namespace. -/
def run {slots : Nat} (space : Namespace) (locals : Locals slots)
    (callee : Operand slots) (arguments : List (Operand slots)) : Result :=
  (callee.eval space locals).bind fun function =>
    (Operand.evalList space locals arguments).bind (invoke function)

end Silmaril.Languages.Python.Core.Module.SeededCall
