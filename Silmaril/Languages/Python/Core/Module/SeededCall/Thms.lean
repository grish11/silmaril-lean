module

public import Silmaril.Languages.Python.Core.Module.SeededCall.Defs
import Silmaril.Proofs.Languages.Python.Core.Module.SeededCall.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Module.SeededCall

theorem Namespace.module_precedes (space : Namespace) {name : String} {value : Value}
    (found : lookupBinding space.moduleGlobals name = some value) : space.lookupGlobal name = some value := by
  simp [Namespace.lookupGlobal, found]

theorem Namespace.builtin_fallback (space : Namespace) {name : String}
    (absent : lookupBinding space.moduleGlobals name = none) :
    space.lookupGlobal name = lookupBinding space.builtins name := by
  simp [Namespace.lookupGlobal, absent]

theorem Namespace.bind_preserves_builtins (space : Namespace) (name : String) (value : Value) :
    (space.bindGlobal name value).builtins = space.builtins := rfl

theorem Operand.eval_local {slots : Nat} (space : Namespace) (locals : Locals slots) (slot : Fin slots) :
    (Operand.local slot).eval space locals =
      (locals.get slot).elim (.error (.raised (.runtime (.unboundLocal slot.val)))) .ok := rfl

theorem Expectation.delivers_iff {expectation : Expectation} {input output : Result} :
    expectation.deliver input = output ↔ Delivers expectation input output :=
  Proofs.Languages.Python.Core.Module.SeededCall.delivers_iff

theorem invoke_iff {callee : Value} {arguments : List Value} {result : Result} :
    invoke callee arguments = result ↔ Executes (Request.decode callee arguments) result :=
  Proofs.Languages.Python.Core.Module.SeededCall.invoke_iff

theorem invoke_assertTrue_true : invoke (.helper .assertTrue) [.bool true] = .ok .none :=
  invoke_iff.mpr .asserted

theorem invoke_assertTrue_false :
    invoke (.helper .assertTrue) [.bool false] = .error (.raised (.assertionError (.boolean false))) :=
  invoke_iff.mpr .assertionFailed

/-- The stock zero-argument constructor returns the canonical empty tuple
payload carried by the seeded value model. -/
theorem invoke_tuple_empty :
    invoke (.builtin .tuple) [] = .ok (.returnedTuple []) :=
  invoke_iff.mpr .emptyTuple

theorem invoke_tuple_exact (items : List Core.Module.TupleDispatch.Element) :
    invoke (.builtin .tuple) [.returnedTuple items] = .ok (.returnedTuple items) :=
  invoke_iff.mpr (.copyTuple items)

theorem invoke_assertTrue_returnedTuple (items : List Core.Module.TupleDispatch.Element) :
    invoke (.helper .assertTrue) [.returnedTuple items] =
      if items.isEmpty then .error (.raised (.assertionError .emptyTuple)) else .ok .none := by
  cases items <;> exact invoke_iff.mpr (by constructor)

theorem invoke_assertTrue_tupleObject (object : Core.Module.TupleDispatch.Object) :
    invoke (.helper .assertTrue) [.tupleObject object] =
      if object.contents.isEmpty then .error (.raised (.assertionError .emptyTuple)) else .ok .none := by
  rcases object with ⟨_, items⟩
  cases items <;> exact invoke_iff.mpr (by constructor)

theorem invoke_tuple_reference (object : Core.Module.TupleDispatch.Object) :
    invoke (.builtin .tuple) [.tupleObject object] = .ok (.tupleObject object) :=
  invoke_iff.mpr (.copyTupleObject object)

theorem run_tuple_reference (space : Namespace) {callee argument : String}
    {descriptor : Core.Module.TupleDispatch.Object}
    (stock : space.lookupGlobal callee = some (.builtin .tuple))
    (found : space.lookupGlobal argument = some (.tupleObject descriptor)) :
    run space #v[] (.global callee) [.global argument] = .ok (.tupleObject descriptor) := by
  simp [run, resolveCall, Operand.evalList, Operand.eval, stock, found, Except.bind, Except.map,
    invoke_tuple_reference]

theorem Namespace.lookup_bindGlobal_same (space : Namespace) (name : String) (value : Value) :
    (space.bindGlobal name value).lookupGlobal name = some value := by
  simp [Namespace.lookupGlobal, Namespace.bindGlobal, lookupBinding]

theorem invoke_int_bool (value : Bool) :
    invoke (.builtin .int) [.bool value] = .ok (.int (Int.ofNat value.toNat)) :=
  invoke_iff.mpr (.intFromBool value)

theorem invoke_stockStr {value : Value} {text : Core.Text} (checked : value.stockStr? = some text) :
    invoke (.builtin .str) [value] = .ok (.text text) := by
  apply invoke_iff.mpr
  simpa [Request.decode, checked] using (Executes.textConversion (arity := 1) text)

theorem invoke_stockBool {value : Value} {result : Bool} (checked : value.stockBool? = some result) :
    invoke (.builtin .bool) [value] = .ok (.bool result) := by
  apply invoke_iff.mpr
  simpa [Request.decode, checked] using (Executes.truthConversion (arity := 1) result)

theorem invoke_assertEqual_text (left right : Core.Text) :
    invoke (.helper .assertEqual) [.text left, .text right] =
      if left = right then .ok .none else .error (.raised (.assertionError (.textPair left right))) := by
  split
  · exact invoke_iff.mpr (.equalText left right ‹_›)
  · exact invoke_iff.mpr (.unequalText left right ‹_›)

theorem invoke_assertEqual_tuple (left right : List Core.Module.TupleDispatch.Element) :
    invoke (.helper .assertEqual) [.returnedTuple left, .returnedTuple right] =
      if Core.Module.TupleDispatch.equalContents left right then .ok .none
      else .error (.raised (.assertionError (.tuplePair left right))) := by
  split
  · exact invoke_iff.mpr (.equalTuple left right ‹_›)
  · exact invoke_iff.mpr (.unequalTuple left right ‹_›)

theorem invoke_assertIsNot_int_bool (integer : Int) (truth : Bool) :
    invoke (.helper .assertIsNot) [.int integer, .bool truth] = .ok .none :=
  invoke_iff.mpr .distinctIntBool

theorem invoke_callable_len :
    invoke (.builtin .callable) [.builtin .len] = .ok (.bool true) :=
  invoke_iff.mpr (.callable .len)

theorem invoke_callable_int (integer : Int) :
    invoke (.builtin .callable) [.int integer] = .ok (.bool false) :=
  invoke_iff.mpr (.callable .integer)

theorem invoke_isinstance_bool_bool (value : Bool) :
    invoke (.builtin .isinstance) [.bool value, .builtin .bool] = .ok (.bool true) :=
  invoke_iff.mpr (.isinstance .boolAgainstBool)

theorem invoke_isinstance_bool_int (value : Bool) :
    invoke (.builtin .isinstance) [.bool value, .builtin .int] = .ok (.bool true) :=
  invoke_iff.mpr (.isinstance .boolAgainstInt)

theorem invoke_isinstance_int_bool (value : Int) :
    invoke (.builtin .isinstance) [.int value, .builtin .bool] = .ok (.bool false) :=
  invoke_iff.mpr (.isinstance .intAgainstBool)

theorem invoke_isinstance_int_int (value : Int) :
    invoke (.builtin .isinstance) [.int value, .builtin .int] = .ok (.bool true) :=
  invoke_iff.mpr (.isinstance .intAgainstInt)

theorem invoke_isinstance_float_float (value : Silmaril.Numeric.Ieee754.F64.Finite) :
    invoke (.builtin .isinstance) [.float64 value, .builtin .float] = .ok (.bool true) :=
  invoke_iff.mpr (.isinstance .floatAgainstFloat)

theorem invoke_isinstance_float_int (value : Silmaril.Numeric.Ieee754.F64.Finite) :
    invoke (.builtin .isinstance) [.float64 value, .builtin .int] = .ok (.bool false) :=
  invoke_iff.mpr (.isinstance .floatAgainstBoolOrInt)

theorem invoke_isinstance_float_bool (value : Silmaril.Numeric.Ieee754.F64.Finite) :
    invoke (.builtin .isinstance) [.float64 value, .builtin .bool] = .ok (.bool false) :=
  invoke_iff.mpr (.isinstance .floatAgainstBoolOrInt)

theorem invoke_isinstance_int_float (value : Int) :
    invoke (.builtin .isinstance) [.int value, .builtin .float] = .ok (.bool false) :=
  invoke_iff.mpr (.isinstance .boolOrIntAgainstFloat)

theorem invoke_isinstance_bool_float (value : Bool) :
    invoke (.builtin .isinstance) [.bool value, .builtin .float] = .ok (.bool false) :=
  invoke_iff.mpr (.isinstance .boolOrIntAgainstFloat)

theorem resolveCall_firstOperandError {slots : Nat} {space : Namespace} {locals : Locals slots}
    {callee operand : Operand slots} {tail : List (Operand slots)} {function : Value} {error : Failure}
    (found : callee.eval space locals = .ok function)
    (failed : operand.eval space locals = .error error) :
    resolveCall space locals callee (operand :: tail) = .error error := by
  simp [resolveCall, Operand.evalList, Except.bind, Except.map, found, failed]

theorem invoke_assertIs_bool (left right : Bool) :
    invoke (.helper .assertIs) [.bool left, .bool right] =
      if BoolIdentity.ofBool left = BoolIdentity.ofBool right then .ok .none
      else .error (.raised (.assertionError (.booleanPair left right))) := by
  split
  · exact invoke_iff.mpr (.sameBool left right ‹_›)
  · exact invoke_iff.mpr (.distinctBool left right ‹_›)

end Silmaril.Languages.Python.Core.Module.SeededCall
