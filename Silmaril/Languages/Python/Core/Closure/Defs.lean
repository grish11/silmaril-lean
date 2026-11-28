module

public import Silmaril.Languages.Python.Core.Binary64.Defs
public import Silmaril.Languages.Python.Core.Module.Dictionary.Defs
public import Silmaril.Languages.Python.Core.Text.Defs

/-! # Slot and cell interfaces for lowered Python closures -/

@[expose] public section

namespace Silmaril.Languages.Python.Core.Closure

/-- Counts of direct locals, frame-owned cells and incoming captures. -/
structure Layout where
  locals : Nat
  owned : Nat
  captures : Nat
  deriving DecidableEq, Repr

inductive Slot (layout : Layout) where
  | local (index : Fin layout.locals)
  | owned (index : Fin layout.owned)
  | capture (index : Fin layout.captures)
  deriving DecidableEq, Repr

/-- Parameters initialize a direct local or a cell owned by the callee. -/
inductive ParameterSlot (layout : Layout) where
  | local (index : Fin layout.locals)
  | owned (index : Fin layout.owned)
  deriving DecidableEq, Repr

def ParameterSlot.slot {layout : Layout} : ParameterSlot layout → Slot layout
  | .local index => .local index
  | .owned index => .owned index

/-- Declaration order for the fixed positional profile. -/
structure Parameters (layout : Layout) where
  slots : List (ParameterSlot layout)
  distinct : slots.Nodup

inductive CaptureSlot (layout : Layout) where
  | owned (index : Fin layout.owned)
  | forwarded (index : Fin layout.captures)
  deriving DecidableEq, Repr

structure CellId where
  address : Nat
  deriving DecidableEq, Repr

/-- A code-table key records the layout expected by its frame. -/
structure CodeRef where
  key : Nat
  layout : Layout
  deriving DecidableEq, Repr

structure Function where
  code : CodeRef
  captures : Vector CellId code.layout.captures
  deriving DecidableEq, Repr

/-- Import a compiler-produced capture list in its existing order. -/
def Function.ofCaptureList (code : CodeRef) (captures : List CellId)
    (size : captures.length = code.layout.captures) : Function :=
  ⟨code, ⟨captures.toArray, by simpa using size⟩⟩

inductive ExceptionClass where
  | exception
  | assertionError
  | nameError
  | unboundLocalError
  | typeError
  | valueError
  | zeroDivisionError
  | overflowError
  | runtimeError
  deriving DecidableEq, Repr

/-- The ancestry relation of the represented stock classes. -/
def ExceptionClass.catches (expected actual : ExceptionClass) : Prop :=
  expected = .exception ∨ expected = actual ∨ (expected = .nameError ∧ actual = .unboundLocalError)

instance (expected actual : ExceptionClass) : Decidable (expected.catches actual) := by
  unfold ExceptionClass.catches
  infer_instance

/-- Exact stock exception payloads for the checked raise forms. -/
inductive ExceptionInstance where
  | empty (kind : ExceptionClass)
  | text (message : Core.Text)
  deriving DecidableEq, Repr

def ExceptionInstance.classify : ExceptionInstance → ExceptionClass
  | .empty kind => kind
  | .text _ => .exception

inductive Value where
  | none
  | int (value : Int)
  | bool (value : Bool)
  | float64 (value : Silmaril.Numeric.Ieee754.F64.Finite)
  | text (value : Core.Text)
  | exceptionClass (kind : ExceptionClass)
  | exceptionInstance (value : ExceptionInstance)
  | function (value : Function)
  | tuple (items : List Core.Module.TupleDispatch.Element)
  | tupleObject (object : Core.Module.TupleDispatch.Object)
  | dictionary (object : Core.Module.Dictionary.Object)
  | dictionaryData (entries : List Core.Module.Dictionary.Entry)
  deriving Repr

@[match_pattern] abbrev Value.stockException : Value := .exceptionClass .exception

def Value.scalar? : Value → Option Core.Module.Value
  | .int value => some (.int value)
  | .bool value => some (.bool value)
  | .none => some .none
  | .float64 _ | .text _ | .exceptionClass _ | .exceptionInstance _ | .function _ | .tuple _ | .tupleObject _
  | .dictionary _ | .dictionaryData _ => Option.none

def Value.ofScalar : Core.Module.Value → Value
  | .int value => .int value
  | .bool value => .bool value
  | .none => .none

def Value.tupleElement? : Value → Option Core.Module.TupleDispatch.Element
  | .text value => some (.text value)
  | value => value.scalar?.map .scalar

def Value.dictionaryRead : Value → Core.Module.Dictionary.ReadValue
  | .dictionary object => .object object
  | value => (value.tupleElement?).elim .unsupported .atom

def Value.ofTupleElement : Core.Module.TupleDispatch.Element → Value
  | .scalar value => Value.ofScalar value
  | .text value => .text value

/-- Only the canonical empty tuple and tuples allocated by the checked
module path expose an identity. An address refers to the originating run. -/
def Value.tupleObject? : Value → Option Core.Module.TupleDispatch.Object
  | .tuple [] => some ⟨Option.none, []⟩
  | .tupleObject object => some object
  | _ => Option.none

/-- The checked items of a flat tuple return. -/
inductive TupleItem (layout : Layout) where
  | literal (value : Core.Module.TupleDispatch.Element)
  | read (slot : Slot layout)
  | global (name : String)
  deriving Repr

/-- A module tuple has scalar literals and live global reads. Its frame
has no local, owned, or captured slots. -/
abbrev GlobalTupleItem := TupleItem ⟨0, 0, 0⟩

def GlobalTupleItem.lower {layout : Layout} : GlobalTupleItem → TupleItem layout
  | .literal value => .literal value
  | .global name => .global name
  | .read (.local slot) | .read (.owned slot) | .read (.capture slot) => Fin.elim0 slot

def GlobalTupleItem.isRead : GlobalTupleItem → Bool
  | .global _ => true
  | _ => false

/-- Complete the ordered reads before checking that every reached value
can be retained as an exact scalar item. -/
def assembleFlatTuple {Item Payload Element Error : Type} (read : Item → Except Error Payload)
    (scalar : Payload → Option Element) (unsupported : Error)
    (items : List Item) : Except Error (List Element) :=
  (items.mapM read).bind fun values =>
    match values.mapM scalar with
    | some checked => .ok checked
    | none => .error unsupported

/-- Python-level errors carried across frames. An unbound incoming capture
corresponds to `NameError`; an unbound local or owned cell to `UnboundLocalError`. -/
inductive RuntimeError where
  | unboundLocal (slot : Nat)
  | unboundOwned (slot : Nat)
  | unboundCapture (slot : Nat)
  | nameError (name : String)
  | positionalArity (expected actual : Nat)
  | notCallable
  | tupleArgumentNotIterable
  | zeroSliceStep
  | additionTypeError
  | multiplicationTypeError
  | assertionError
  | raisedInstance (value : ExceptionInstance)
  | invalidRaiseOperand
  | invalidHandlerClass
  | noActiveException
  | arithmetic (error : Exception)
  | overflowError
  deriving DecidableEq, Repr

@[match_pattern] abbrev RuntimeError.explicitException (message : Core.Text) : RuntimeError :=
  .raisedInstance (.text message)

@[simp] def RuntimeError.classify : RuntimeError → ExceptionClass
  | .assertionError => .assertionError
  | .unboundLocal _ | .unboundOwned _ => .unboundLocalError
  | .unboundCapture _ | .nameError _ => .nameError
  | .positionalArity .. | .notCallable | .additionTypeError | .multiplicationTypeError
  | .tupleArgumentNotIterable | .invalidHandlerClass | .invalidRaiseOperand => .typeError
  | .zeroSliceStep => .valueError
  | .arithmetic .zeroDivisionError => .zeroDivisionError
  | .overflowError => .overflowError
  | .raisedInstance instanceValue => instanceValue.classify
  | .noActiveException => .runtimeError

/-- The target binding can retain an explicit instance or an empty assertion.
Other runtime errors require their exception object payload to be modeled. -/
def RuntimeError.handlerInstance? : RuntimeError → Option ExceptionInstance
  | .raisedInstance value => some value
  | .assertionError => some (.empty .assertionError)
  | _ => none

/-- Invalid runtime references are distinct from defined Python exceptions. -/
inductive Failure where
  | defined (error : RuntimeError)
  | danglingCell (identity : CellId)
  | unsupportedTupleElement
  | unsupportedFloatOperand
  | unsupportedDictionaryOperand
  | unsupportedCallable
  deriving DecidableEq, Repr

/-- Integer-like values in the closed closure value profile. -/
def Value.asInt? : Value → Option Int
  | .int value => some value
  | .bool false => some 0
  | .bool true => some 1
  | .none | .float64 _ | .text _ | .exceptionClass _ | .exceptionInstance _ | .function _ | .tuple _ | .tupleObject _
  | .dictionary _ | .dictionaryData _ => Option.none

/-- Integer equality is checked before a comparison can consume a float. -/
def Value.equalInt : Value → Int → Except Failure Value
  | .float64 _, _ => .error .unsupportedFloatOperand
  | .int value, right => .ok (.bool (decide (value = right)))
  | .bool false, right => .ok (.bool (decide (0 = right)))
  | .bool true, right => .ok (.bool (decide (1 = right)))
  | .none, _ | .text _, _ | .exceptionClass _, _ | .exceptionInstance _, _ | .function _, _ | .tuple _, _ | .tupleObject _, _
  | .dictionary _, _ | .dictionaryData _, _ => .ok (.bool false)

inductive IntegerOp where
  | add
  | mul
  deriving DecidableEq, Repr

def IntegerOp.eval : IntegerOp → Int → Int → Int
  | .add, lhs, rhs => lhs + rhs
  | .mul, lhs, rhs => lhs * rhs

def IntegerOp.typeError : IntegerOp → RuntimeError
  | .add => .additionTypeError
  | .mul => .multiplicationTypeError

/-- Apply exact integer arithmetic after both operands have been read.
The other modeled values include None, functions and flat tuples. -/
def Value.binaryInt (op : IntegerOp) (left right : Value) : Except Failure Value :=
  match left, right with
  | .float64 _, _ | _, .float64 _ => .error .unsupportedFloatOperand
  | _, _ =>
    match left.asInt?, right.asInt? with
    | some lhs, some rhs => .ok (.int (op.eval lhs rhs))
    | _, _ => .error (.defined op.typeError)

abbrev Value.addInt := Value.binaryInt .add

abbrev Result := Except RuntimeError Value

/-- Exact integer floor division and its matching divisor-signed remainder. -/
inductive IntDivModOp where
  | floorDiv
  | modulo

def IntDivModOp.eval (op : IntDivModOp) (numerator divisor : Int) : Except RuntimeError Int :=
  if divisor = 0 then .error (.arithmetic .zeroDivisionError)
  else .ok (match op with
    | .floorDiv => numerator.fdiv divisor
    | .modulo => numerator.fmod divisor)

def trueDivideInt (numerator divisor : Int) : Except RuntimeError Silmaril.Numeric.Ieee754.F64.Finite :=
  (Core.Binary64.trueDivide numerator divisor).mapError fun
    | .zeroDivisionError => .arithmetic .zeroDivisionError
    | .overflowError => .overflowError

def floatDivisionResult
    (result : Except Core.Binary64.FloatDivisionError Silmaril.Numeric.Ieee754.F64.Finite) :
    Except Failure Silmaril.Numeric.Ieee754.F64.Finite :=
  result.mapError fun
    | .conversionOverflow => .defined .overflowError
    | .zeroDivisionError => .defined (.arithmetic .zeroDivisionError)
    | .nonfiniteResult => .unsupportedFloatOperand

def trueDivideFloat (operands : Core.Binary64.FloatOperands) : Except Failure Silmaril.Numeric.Ieee754.F64.Finite :=
  floatDivisionResult (Core.Binary64.divideFloat operands)

def floatDivMod (op : Core.Binary64.FloatDivModOp) (operands : Core.Binary64.FloatOperands) :
    Except Failure Silmaril.Numeric.Ieee754.F64.Finite :=
  floatDivisionResult (op.eval operands)

def floatArithmeticResult
    (result : Except Core.Binary64.FloatArithmeticError Silmaril.Numeric.Ieee754.F64.Finite) :
    Except Failure Value :=
  result.map .float64 |>.mapError fun
    | .conversionOverflow => .defined .overflowError
    | .nonfiniteResult => .unsupportedFloatOperand

def mixedAdd (integer : Int) (floating : Silmaril.Numeric.Ieee754.F64.Finite) : Except Failure Value :=
  floatArithmeticResult (Core.Binary64.mixedAdd integer floating)

def floatAdd (left right : Silmaril.Numeric.Ieee754.F64.Finite) : Except Failure Value :=
  (Core.Binary64.addFinite? left right).elim (.error .unsupportedFloatOperand) (.ok ∘ Value.float64)

def floatSub (operands : Core.Binary64.FloatOperands) : Except Failure Value :=
  floatArithmeticResult (Core.Binary64.subtract operands)

def floatMul (operands : Core.Binary64.FloatOperands) : Except Failure Value :=
  floatArithmeticResult (Core.Binary64.multiply operands)

/-- A shared heap with monotone cell allocation. Only addresses below
`next` denote allocated cells. An allocated cell may be unbound. -/
structure Heap where
  next : Nat
  contents : Nat → Option Value

def Heap.empty : Heap := ⟨0, fun _ => none⟩

def Heap.lookup (heap : Heap) (identity : CellId) : Option (Option Value) :=
  if identity.address < heap.next then some (heap.contents identity.address) else none

def Heap.reserve (heap : Heap) (count : Nat) : Heap :=
  ⟨heap.next + count, fun address => if address < heap.next then heap.contents address else none⟩

def Heap.write (heap : Heap) (identity : CellId) (value : Value) : Option Heap :=
  if identity.address < heap.next then
    some ⟨heap.next, fun address => if address = identity.address then some value else heap.contents address⟩
  else none

/-- Append one initialized slot using the same monotone frontier as
owned cells. The previous slots retain their contents and addresses. -/
def Heap.allocate (heap : Heap) (value : Value) : CellId × Heap :=
  let identity : CellId := ⟨heap.next⟩
  let reached := heap.reserve 1
  (identity, { reached with contents := fun address =>
    if address = identity.address then some value else reached.contents address })

/-- The namespace carries an address. Only the allocated slot carries the
entries, so rebinding or copying a handle does not copy the dictionary. -/
def Heap.materializeDictionary (heap : Heap) (display : List Core.Module.Dictionary.Entry) :
    Core.Module.Dictionary.Object × Heap :=
  let (cell, reached) := heap.allocate (.dictionaryData (Core.Module.Dictionary.build display))
  (⟨cell.address⟩, reached)

def Heap.dictionaryEntries? (heap : Heap) (object : Core.Module.Dictionary.Object) :
    Option (List Core.Module.Dictionary.Entry) :=
  match heap.lookup ⟨object.address⟩ with
  | some (some (.dictionaryData entries)) => some entries
  | _ => none

def Value.truth (value : Value) (heap : Heap) : Bool :=
  match value with
  | .none => false
  | .int value => decide (value ≠ 0)
  | .bool value => value
  | .float64 value => !value.val.isZero
  | .text value => value.truth
  | .exceptionClass _ | .exceptionInstance _ | .function _ => true
  | .tuple items => !items.isEmpty
  | .tupleObject object => !object.contents.isEmpty
  | .dictionary object => (heap.dictionaryEntries? object).any (!·.isEmpty)
  | .dictionaryData .. => false

def dictionaryFailure : Core.Module.Dictionary.Failure → Failure
  | .missingName name => .defined (.nameError name)
  | .clearArity actual => .defined (.positionalArity 0 actual)
  | .unsupported => .unsupportedDictionaryOperand

def evalDictionaryGet (heap : Heap) (globals : String → Option Value)
    (test : Core.Module.Dictionary.Get) : Except Failure Value :=
  (test.eval (fun name => (globals name).map Value.dictionaryRead) heap.dictionaryEntries?).map
    Value.ofTupleElement |>.mapError dictionaryFailure

def clearDictionary (heap : Heap) (globals : String → Option Core.Module.Dictionary.ReadValue)
    (call : Core.Module.Dictionary.Clear) : Except Core.Module.Dictionary.Failure Heap := do
  let object ← call.prepare globals heap.dictionaryEntries?
  let some reached := heap.write ⟨object.address⟩ (.dictionaryData []) | throw .unsupported
  return reached

/-- Save a positive witness for the evaluated constant. Its heap slot
records the descriptor itself, so it is distinct from a fresh-object slot
holding a tuple payload. Two such witnesses may refer to one Python constant. -/
def Heap.saveTupleOrigin (heap : Heap) (head : Core.Module.TupleDispatch.Element) (tail : List Core.Module.TupleDispatch.Element) :
    Core.Module.TupleDispatch.Object × Heap :=
  let descriptor : Core.Module.TupleDispatch.Object := ⟨some heap.next, head :: tail⟩
  (descriptor, (heap.allocate (.tupleObject descriptor)).2)

/-- Materialize a new exact tuple. The empty tuple keeps its canonical
representation and needs no allocation. -/
def Heap.materializeFreshTuple (heap : Heap) (contents : List Core.Module.TupleDispatch.Element) : Value × Heap :=
  match contents with
  | [] => (.tuple [], heap)
  | _ :: _ =>
    let (reference, reached) := heap.allocate (.tuple contents)
    (.tupleObject ⟨some reference.address, contents⟩, reached)

/-- A display with a live item read builds a fresh object. A closed
nonempty display can save its origin when identity is observed. Empty
tuples need no heap slot. -/
def Heap.materializeModuleTuple (heap : Heap) (items : List GlobalTupleItem)
    (contents : List Core.Module.TupleDispatch.Element) (trackClosed : Bool := false) : Value × Heap :=
  match contents with
  | [] => (.tuple [], heap)
  | head :: tail =>
    if items.any GlobalTupleItem.isRead then heap.materializeFreshTuple contents
    else if trackClosed then
      let (descriptor, reached) := heap.saveTupleOrigin head tail
      (.tupleObject descriptor, reached)
    else (.tuple contents, heap)

structure Frame (layout : Layout) where
  locals : Fin layout.locals → Option Value
  owned : Fin layout.owned → CellId
  captures : Fin layout.captures → CellId

variable {layout : Layout}

/-- Allocate owned cells in slot order. Incoming captures keep their identities. -/
def Frame.fresh (heap : Heap) (captures : Fin layout.captures → CellId) : Heap × Frame layout :=
  (heap.reserve layout.owned,
    ⟨fun _ => none, fun slot => ⟨heap.next + slot.val⟩, captures⟩)

def Function.freshFrame (fn : Function) (heap : Heap) : Heap × Frame fn.code.layout :=
  Frame.fresh heap fn.captures.get

def Frame.captureCell (frame : Frame layout) : CaptureSlot layout → CellId
  | .owned index => frame.owned index
  | .forwarded index => frame.captures index

/-- Use the child's index order and retain each selected parent identity. -/
def Frame.closure (frame : Frame layout) (code : CodeRef)
    (select : Fin code.layout.captures → CaptureSlot layout) : Function :=
  ⟨code, Vector.ofFn (frame.captureCell ∘ select)⟩

def Heap.read (heap : Heap) (identity : CellId) (unbound : RuntimeError) : Except Failure Value :=
  match heap.lookup identity with
  | none => .error (.danglingCell identity)
  | some none => .error (.defined unbound)
  | some (some value) => .ok value

def Frame.read (frame : Frame layout) (heap : Heap) : Slot layout → Except Failure Value
  | .local index =>
    match frame.locals index with
    | none => .error (.defined (.unboundLocal index.val))
    | some value => .ok value
  | .owned index => heap.read (frame.owned index) (.unboundOwned index.val)
  | .capture index => heap.read (frame.captures index) (.unboundCapture index.val)

def Frame.writeCell (frame : Frame layout) (heap : Heap) (identity : CellId)
    (value : Value) : Except Failure (Heap × Frame layout) :=
  match heap.write identity value with
  | none => .error (.danglingCell identity)
  | some heap' => .ok (heap', frame)

def Frame.write (frame : Frame layout) (heap : Heap) (slot : Slot layout)
    (value : Value) : Except Failure (Heap × Frame layout) :=
  match slot with
  | .local index =>
    .ok (heap, { frame with locals := fun slot => if slot = index then some value else frame.locals slot })
  | .owned index => frame.writeCell heap (frame.owned index) value
  | .capture index => frame.writeCell heap (frame.captures index) value

end Silmaril.Languages.Python.Core.Closure
