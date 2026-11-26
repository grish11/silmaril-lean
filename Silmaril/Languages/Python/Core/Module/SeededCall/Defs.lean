module

public import Silmaril.Languages.Python.Core.Closure.Defs
public import Silmaril.Languages.Python.Core.Module.ListObject.Defs
public import Silmaril.Languages.Python.Core.Module.TupleDispatch.Defs
public import Silmaril.Languages.Python.Core.Text.Slice.Defs

/-! # Closed callables for explicitly seeded module entry -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Module.SeededCall

open Core.Closure (RuntimeError)
open Core.Binary64 (NumericOperand)
open Core.Module.TupleDispatch (equalContents)

inductive ExceptionClass where
  | assertionError
  | nameError
  | unboundLocalError
  | typeError
  | valueError
  | zeroDivisionError
  | overflowError
  deriving DecidableEq, Repr

inductive AssertionArgument where
  | empty
  | text (message : String)
  | integerPair (left right : Int)
  | numericPair (left right : NumericOperand)
  | boolean (value : Bool)
  | booleanPair (left right : Bool)
  | textPair (left right : Core.Text)
  | tuplePair (left right : List Core.Module.TupleDispatch.Element)
  | emptyTuple
  deriving DecidableEq, Repr

inductive Raised where
  | assertionError (argument : AssertionArgument)
  | runtime (error : RuntimeError)
  deriving DecidableEq, Repr

def Raised.classify : Raised → ExceptionClass
  | .assertionError _ | .runtime .assertionError => .assertionError
  | .runtime (.unboundLocal _) | .runtime (.unboundOwned _) => .unboundLocalError
  | .runtime (.unboundCapture _) | .runtime (.nameError _) => .nameError
  | .runtime (.positionalArity ..) | .runtime .notCallable | .runtime .additionTypeError
  | .runtime .multiplicationTypeError | .runtime .tupleArgumentNotIterable => .typeError
  | .runtime .zeroSliceStep => .valueError
  | .runtime (.arithmetic .zeroDivisionError) => .zeroDivisionError
  | .runtime .overflowError => .overflowError

def ExceptionClass.catches (expected actual : ExceptionClass) : Prop :=
  expected = actual ∨ (expected = .nameError ∧ actual = .unboundLocalError)

instance (expected actual : ExceptionClass) : Decidable (expected.catches actual) := by
  unfold ExceptionClass.catches
  infer_instance

inductive Helper where
  | assertEqual
  | assertTrue
  | assertIs
  | assertIsNot
  | assertRaises (onReturn : AssertionArgument)
  deriving DecidableEq, Repr

inductive Builtin where
  | int
  | bool
  | float
  | callable
  | len
  | ord
  | list
  | tuple
  | isinstance
  | str
  deriving DecidableEq, Repr

inductive Value where
  | int (value : Int)
  | bool (value : Bool)
  | float64 (value : Silmaril.Numeric.Ieee754.F64.Finite)
  | text (value : Core.Text)
  | none
  | listObject (object : Core.Module.ListObject)
  | returnedTuple (items : List Core.Module.TupleDispatch.Element)
  | tupleObject (object : Core.Module.TupleDispatch.Object)
  | exceptionClass (kind : ExceptionClass)
  | helper (descriptor : Helper)
  | builtin (descriptor : Builtin)
  | function (closure : Core.Closure.Function)
  deriving DecidableEq, Repr

def Value.scalar? : Value → Option Core.Module.Value
  | .int value => some (.int value)
  | .bool value => some (.bool value)
  | .none => some .none
  | .float64 _ | .text _ | .exceptionClass _ | .helper _ | .builtin _ | .function _ | .listObject _
  | .returnedTuple _ | .tupleObject _ => Option.none

def Value.ofScalar : Core.Module.Value → Value
  | .int value => .int value
  | .bool value => .bool value
  | .none => .none

def Value.tupleElement? : Value → Option Core.Module.TupleDispatch.Element
  | .text value => some (.text value)
  | value => value.scalar?.map .scalar

def Value.ofTupleElement : Core.Module.TupleDispatch.Element → Value
  | .scalar value => Value.ofScalar value
  | .text value => .text value

def Value.stockStr? : Value → Option Core.Text
  | .int value => Core.Text.decimal? value
  | .bool value => some (Core.Text.ofString (if value then "True" else "False"))
  | .text value => some value
  | .none => some (Core.Text.ofString "None")
  | _ => Option.none

def Value.stockBool? : Value → Option Bool
  | .text value => some value.truth
  | value => value.scalar?.map Core.Module.Value.truth

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
  | intTrueDiv (numerator divisor : Int)
  | mixedAdd (integer : Int) (floating : Silmaril.Numeric.Ieee754.F64.Finite)
  | floatAdd (left right : Silmaril.Numeric.Ieee754.F64.Finite)
  | local (slot : Fin slots)
  | global (name : String)
  | tuple (items : List Core.Closure.GlobalTupleItem)
  | textSlice (receiver : Core.Text) (bounds : Core.SliceBounds)
  | unsupported

abbrev Locals (slots : Nat) := Vector (Option Value) slots

def readTupleItem (space : Namespace) : Core.Closure.GlobalTupleItem → Result
  | .literal value => .ok (Value.ofTupleElement value)
  | .global name =>
    (space.lookupGlobal name).elim (.error (.raised (.runtime (.nameError name)))) .ok
  | .read (.local slot) | .read (.owned slot) | .read (.capture slot) => Fin.elim0 slot

def evalTupleContents (space : Namespace) (items : List Core.Closure.GlobalTupleItem) :
    Except Failure (List Core.Module.TupleDispatch.Element) :=
  Core.Closure.assembleFlatTuple (readTupleItem space) Value.tupleElement? .unsupported items

def Operand.eval {slots : Nat} (space : Namespace) (locals : Locals slots) : Operand slots → Result
  | .literal value => .ok value
  | .intTrueDiv numerator divisor =>
    (Core.Closure.trueDivideInt numerator divisor).map Value.float64 |>.mapError (Failure.raised ∘ .runtime)
  | .mixedAdd integer floating =>
    (Core.Binary64.mixedAdd integer floating).map Value.float64 |>.mapError fun
      | .conversionOverflow => .raised (.runtime .overflowError)
      | .nonfiniteResult => .unsupported
  | .floatAdd left right =>
    (Core.Binary64.addFinite? left right).elim (.error .unsupported) (.ok ∘ Value.float64)
  | .local slot =>
    (locals.get slot).elim (.error (.raised (.runtime (.unboundLocal slot.val)))) .ok
  | .global name =>
    (space.lookupGlobal name).elim (.error (.raised (.runtime (.nameError name)))) .ok
  | .tuple items =>
    (evalTupleContents space items).map .returnedTuple
  | .textSlice receiver bounds =>
    (receiver.slice? bounds).elim (.error (.raised (.runtime .zeroSliceStep))) (fun result => .ok (.text result))
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

/-- Exact Booleans refer to the two canonical Python singleton objects. -/
inductive BoolIdentity where
  | falseObject
  | trueObject
  deriving DecidableEq

def BoolIdentity.ofBool : Bool → BoolIdentity
  | false => .falseObject
  | true => .trueObject

/-- Only the stock `len` object and exact integers are probed. -/
inductive CallableProbe where
  | len
  | integer

def CallableProbe.result : CallableProbe → Bool
  | .len => true
  | .integer => false

/-- Exact Boolean, integer, and finite float values against the stock numeric classes. -/
inductive InstanceProbe where
  | boolAgainstBool
  | boolAgainstInt
  | intAgainstBool
  | intAgainstInt
  | floatAgainstFloat
  | floatAgainstBoolOrInt
  | boolOrIntAgainstFloat

def InstanceProbe.result : InstanceProbe → Bool
  | .boolAgainstBool | .boolAgainstInt | .intAgainstInt | .floatAgainstFloat => true
  | .intAgainstBool | .floatAgainstBoolOrInt | .boolOrIntAgainstFloat => false

/-- Decoding identifies the admitted typed call shapes. In particular,
calling an exception class would construct an object outside this profile. -/
inductive Request (arity : Nat) where
  | assertBoolean (value : Bool)
  | assertTuple (nonempty : Bool)
  | compare (left right : Int)
  | compareNumeric (left right : NumericOperand)
  | compareText (left right : Core.Text)
  | compareTuple (left right : List Core.Module.TupleDispatch.Element)
  | textConversion (result : Core.Text)
  | truthConversion (result : Bool)
  | intFromBool (value : Bool)
  | callable (probe : CallableProbe)
  | isinstance (probe : InstanceProbe)
  | boolIdentity (left right : Bool)
  | distinctIntBool
  | emptyTuple
  | copyTuple (items : List Core.Module.TupleDispatch.Element)
  | copyTupleObject (object : Core.Module.TupleDispatch.Object)
  | expect (expectation : Expectation) (callback : Value) (arguments : List Value)
      (shorter : arguments.length < arity)
  | nonCallable
  | unsupported

def Request.decode (callee : Value) (arguments : List Value) : Request arguments.length :=
  match callee, arguments with
  | .helper .assertTrue, [.bool result] => .assertBoolean result
  | .helper .assertTrue, [.returnedTuple items]
  | .helper .assertTrue, [.tupleObject ⟨_, items⟩] => .assertTuple (!items.isEmpty)
  | .helper .assertEqual, [.int left, .int right] => .compare left right
  | .helper .assertEqual, [.float64 left, .float64 right] => .compareNumeric (.float64 left) (.float64 right)
  | .helper .assertEqual, [.float64 left, .int right] => .compareNumeric (.float64 left) (.integer right)
  | .helper .assertEqual, [.int left, .float64 right] => .compareNumeric (.integer left) (.float64 right)
  | .helper .assertEqual, [.text left, .text right] => .compareText left right
  | .helper .assertEqual, [.returnedTuple left, .returnedTuple right] => .compareTuple left right
  | .helper .assertEqual, [.tupleObject left, .returnedTuple right] => .compareTuple left.contents right
  | .helper .assertEqual, [.returnedTuple left, .tupleObject right] => .compareTuple left right.contents
  | .helper .assertEqual, [.tupleObject left, .tupleObject right] => .compareTuple left.contents right.contents
  | .builtin .str, [] => .textConversion (Core.Text.ofString "")
  | .builtin .str, [value] => (value.stockStr?).elim .unsupported .textConversion
  | .builtin .bool, [] => .truthConversion false
  | .builtin .bool, [value] => (value.stockBool?).elim .unsupported .truthConversion
  | .builtin .int, [.bool value] => .intFromBool value
  | .builtin .tuple, [] => .emptyTuple
  | .builtin .callable, [.builtin .len] => .callable .len
  | .builtin .callable, [.int _] => .callable .integer
  | .builtin .isinstance, [.bool _, .builtin .bool] => .isinstance .boolAgainstBool
  | .builtin .isinstance, [.bool _, .builtin .int] => .isinstance .boolAgainstInt
  | .builtin .isinstance, [.int _, .builtin .bool] => .isinstance .intAgainstBool
  | .builtin .isinstance, [.int _, .builtin .int] => .isinstance .intAgainstInt
  | .builtin .isinstance, [.float64 _, .builtin .float] => .isinstance .floatAgainstFloat
  | .builtin .isinstance, [.float64 _, .builtin .bool]
  | .builtin .isinstance, [.float64 _, .builtin .int] => .isinstance .floatAgainstBoolOrInt
  | .builtin .isinstance, [.bool _, .builtin .float]
  | .builtin .isinstance, [.int _, .builtin .float] => .isinstance .boolOrIntAgainstFloat
  | .helper .assertIs, [.bool left, .bool right] => .boolIdentity left right
  | .helper .assertIsNot, [.int _, .bool _] | .helper .assertIsNot, [.bool _, .int _] => .distinctIntBool
  | .helper (.assertRaises onReturn), .exceptionClass expected :: callback :: arguments =>
    .expect ⟨expected, onReturn⟩ callback arguments (by simp only [List.length_cons]; omega)
  | .builtin .tuple, [.returnedTuple items] => .copyTuple items
  | .builtin .tuple, [.tupleObject object] => .copyTupleObject object
  | .none, _ | .int _, _ | .bool _, _ | .float64 _, _ | .text _, _ | .listObject _, _ | .returnedTuple _, _
  | .tupleObject _, _ => .nonCallable
  | _, _ => .unsupported

/-- Invoking an expectation calls the supplied closed callable using the
same dispatcher as a direct call. -/
def invoke (callee : Value) (arguments : List Value) : Result :=
  match Request.decode callee arguments with
  | .assertBoolean true => .ok .none
  | .assertBoolean false => .error (.raised (.assertionError (.boolean false)))
  | .assertTuple true => .ok .none
  | .assertTuple false => .error (.raised (.assertionError .emptyTuple))
  | .compare left right =>
    if left = right then .ok .none else .error (.raised (.assertionError (.integerPair left right)))
  | .compareNumeric left right =>
    if left.equal right then .ok .none else .error (.raised (.assertionError (.numericPair left right)))
  | .compareText left right =>
    if left = right then .ok .none else .error (.raised (.assertionError (.textPair left right)))
  | .compareTuple left right =>
    if equalContents left right then .ok .none
    else .error (.raised (.assertionError (.tuplePair left right)))
  | .textConversion value => .ok (.text value)
  | .truthConversion value => .ok (.bool value)
  | .intFromBool value => .ok (.int (Int.ofNat value.toNat))
  | .callable probe => .ok (.bool probe.result)
  | .isinstance probe => .ok (.bool probe.result)
  | .boolIdentity left right =>
    if BoolIdentity.ofBool left = BoolIdentity.ofBool right then .ok .none
    else .error (.raised (.assertionError (.booleanPair left right)))
  | .distinctIntBool => .ok .none
  | .emptyTuple => .ok (.returnedTuple [])
  | .copyTuple items => .ok (.returnedTuple items)
  | .copyTupleObject object => .ok (.tupleObject object)
  | .expect expectation callback args _shorter =>
    expectation.deliver (invoke callback args)
  | .nonCallable => .error (.raised (.runtime .notCallable))
  | .unsupported => .error .unsupported
termination_by arguments.length

inductive Executes : {arity : Nat} → Request arity → Result → Prop where
  | asserted {arity : Nat} : Executes (arity := arity) (.assertBoolean true) (.ok .none)
  | assertionFailed {arity : Nat} :
      Executes (arity := arity) (.assertBoolean false) (.error (.raised (.assertionError (.boolean false))))
  | tupleAsserted {arity : Nat} : Executes (arity := arity) (.assertTuple true) (.ok .none)
  | tupleAssertionFailed {arity : Nat} :
      Executes (arity := arity) (.assertTuple false) (.error (.raised (.assertionError .emptyTuple)))
  | equal {arity : Nat} (left right : Int) (same : left = right) :
      Executes (arity := arity) (.compare left right) (.ok .none)
  | unequal {arity : Nat} (left right : Int) (different : left ≠ right) :
      Executes (arity := arity) (.compare left right) (.error (.raised (.assertionError (.integerPair left right))))
  | equalNumeric {arity : Nat} (left right : NumericOperand) (same : left.equal right = true) :
      Executes (arity := arity) (.compareNumeric left right) (.ok .none)
  | unequalNumeric {arity : Nat} (left right : NumericOperand) (different : left.equal right ≠ true) :
      Executes (arity := arity) (.compareNumeric left right)
        (.error (.raised (.assertionError (.numericPair left right))))
  | equalText {arity : Nat} (left right : Core.Text) (same : left = right) :
      Executes (arity := arity) (.compareText left right) (.ok .none)
  | unequalText {arity : Nat} (left right : Core.Text) (different : left ≠ right) :
      Executes (arity := arity) (.compareText left right)
        (.error (.raised (.assertionError (.textPair left right))))
  | equalTuple {arity : Nat} (left right : List Core.Module.TupleDispatch.Element) (same : equalContents left right = true) :
      Executes (arity := arity) (.compareTuple left right) (.ok .none)
  | unequalTuple {arity : Nat} (left right : List Core.Module.TupleDispatch.Element) (different : equalContents left right ≠ true) :
      Executes (arity := arity) (.compareTuple left right)
        (.error (.raised (.assertionError (.tuplePair left right))))
  | textConversion {arity : Nat} (value : Core.Text) :
      Executes (arity := arity) (.textConversion value) (.ok (.text value))
  | truthConversion {arity : Nat} (value : Bool) :
      Executes (arity := arity) (.truthConversion value) (.ok (.bool value))
  | intFromBool {arity : Nat} (value : Bool) :
      Executes (arity := arity) (.intFromBool value) (.ok (.int (Int.ofNat value.toNat)))
  | callable {arity : Nat} (probe : CallableProbe) :
      Executes (arity := arity) (.callable probe) (.ok (.bool probe.result))
  | isinstance {arity : Nat} (probe : InstanceProbe) :
      Executes (arity := arity) (.isinstance probe) (.ok (.bool probe.result))
  | sameBool {arity : Nat} (left right : Bool)
      (same : BoolIdentity.ofBool left = BoolIdentity.ofBool right) :
      Executes (arity := arity) (.boolIdentity left right) (.ok .none)
  | distinctBool {arity : Nat} (left right : Bool)
      (different : BoolIdentity.ofBool left ≠ BoolIdentity.ofBool right) :
      Executes (arity := arity) (.boolIdentity left right)
        (.error (.raised (.assertionError (.booleanPair left right))))
  | distinctIntBool {arity : Nat} : Executes (arity := arity) .distinctIntBool (.ok .none)
  | emptyTuple {arity : Nat} : Executes (arity := arity) .emptyTuple (.ok (.returnedTuple []))
  | copyTuple {arity : Nat} (items : List Core.Module.TupleDispatch.Element) :
      Executes (arity := arity) (.copyTuple items) (.ok (.returnedTuple items))
  | copyTupleObject {arity : Nat} (object : Core.Module.TupleDispatch.Object) :
      Executes (arity := arity) (.copyTupleObject object) (.ok (.tupleObject object))
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

def resolveCall {slots : Nat} (space : Namespace) (locals : Locals slots)
    (callee : Operand slots) (arguments : List (Operand slots)) :
    Except Failure (Value × List Value) :=
  (callee.eval space locals).bind fun function =>
    (Operand.evalList space locals arguments).map (function, ·)

/-- Resolve the callable, then resolve positional operands in order. Calls
and their supported callback do not write either namespace. -/
def run {slots : Nat} (space : Namespace) (locals : Locals slots)
    (callee : Operand slots) (arguments : List (Operand slots)) : Result :=
  (resolveCall space locals callee arguments).bind fun (function, values) => invoke function values

end Silmaril.Languages.Python.Core.Module.SeededCall
