module

public import Silmaril.Languages.Starlark.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists

/-- An index in the shared heap. Allocation appends a fresh cell. -/
abbrev Address := Nat

/-- Universal callables supported by the resolved shared-store profile. -/
inductive Builtin where
  | bool | len | type | list | tuple
  deriving DecidableEq, BEq, Repr

def Builtin.name : Builtin → String
  | .bool => "bool"
  | .len => "len"
  | .type => "type"
  | .list => "list"
  | .tuple => "tuple"

/-- Resolve a name after lexical lookup has ruled out a shadowing binding. -/
def Builtin.resolve (name : String) : Option Builtin :=
  ([.bool, .len, .type, .list, .tuple] : List Builtin).find? (fun id => id.name == name)

inductive Value where
  | scalar (value : Starlark.Value)
  | list (address : Address)
  | tuple (address : Address)
  | dict (address : Address)
  | function (address : Address)
  | builtin (id : Builtin)
  | string (text : String)
  deriving DecidableEq, Repr

def Value.address? : Value → Option Address
  | .list address | .tuple address | .dict address | .function address => some address
  | .scalar _ | .builtin _ | .string _ => none

/-- Canonical key encoding for tagged scalars and well-bracketed tuples. -/
inductive KeyPart where
  | scalar (value : Starlark.Value)
  | openTuple
  | closeTuple
  | function (address : Address)
  | builtin (id : Builtin)
  | string (text : String)
  deriving DecidableEq, BEq, Repr

abbrev Key := List KeyPart

structure Entry where
  key : Value
  keyCode : Key
  value : Value
  deriving DecidableEq, Repr

/-- One free name in the callee, with the address of its defining slot. -/
structure Capture where
  binding : Binding
  address : Address
  localCell : Bool
  deriving DecidableEq, Repr

structure Closure where
  declaration : Nat
  captures : List Capture
  defaults : List (Binding × Value)
  deriving DecidableEq, Repr

inductive Contents where
  | list (elements : List Value)
  | tuple (elements : List Value) (keyCode : Option Key)
  | dict (entries : List Entry)
  | binding (value : Option Value)
  | function (closure : Closure)
  deriving DecidableEq, Repr

def Contents.children : Contents → List Address
  | .list elements | .tuple elements _ => elements.filterMap Value.address?
  | .dict entries => (entries.flatMap fun entry => [entry.key, entry.value]).filterMap Value.address?
  | .binding value => value.toList.filterMap Value.address?
  | .function closure =>
    (closure.captures.filterMap fun capture =>
      if capture.localCell then some capture.address else none) ++
    (closure.defaults.filterMap fun (_, value) => value.address?)

def Contents.sameMutableKind : Contents → Contents → Bool
  | .list _, .list _ | .dict _, .dict _ => true
  | _, _ => false

structure Cell where
  contents : Contents
  frozen : Bool := false
  deriving DecidableEq, Repr

abbrev Heap := Array Cell

inductive Slot where
  | owned (address : Address)
  | captured (address : Address) (localCell : Bool)
  deriving DecidableEq, Repr

def Slot.address : Slot → Address
  | .owned address | .captured address _ => address

structure State where
  heap : Heap := #[]
  bindings : Binding → Option Value := fun _ => none
  slots : Binding → Option Slot := fun _ => none
  /-- One entry per active list iterator, with the innermost iterator first. -/
  iterators : List Address := []

inductive Error where
  | uninitialized (binding : Binding)
  | danglingAddress (address : Address)
  | indexTarget
  | indexType
  | indexRange (index : Int) (length : Nat)
  | assignmentTarget
  | appendTarget
  | frozen (address : Address)
  | activeIteration (address : Address)
  | notIterable
  | wrongCellKind (address : Address)
  | unhashableKey (value : Value)
  | missingKey (key : Value)
  | duplicateKey (key : Value)
  | unknownDeclaration (declaration : Nat)
  | missingCapture (binding : Binding)
  | notCallable
  | arity (expected supplied : Nat)
  | recursiveCall (declaration : Nat)
  | invalidStar
  | invalidStarStar
  | keywordMustBeString (key : Value)
  | unexpectedKeyword (name : String)
  | multipleArgumentValues (name : String)
  | missingArguments (names : List String)
  | builtinArity (id : Builtin) (minimum maximum supplied : Nat)
  | builtinKeyword (id : Builtin) (name : String)
  | builtinType (id : Builtin) (value : Value)
  deriving DecidableEq, Repr

abbrev Outcome := EStateM.Result Error State
abbrev Meaning := EStateM Error State

/-- Apply one primitive to an operand result, preserving its state on failure. -/
def Outcome.resume {α β : Type} (out : Outcome α) (primitive : α → Meaning β) : Outcome β :=
  match out with
  | .ok value state => primitive value state
  | .error error state => .error error state

def State.bindingValue (state : State) (binding : Binding) : Except Error Value :=
  let value : Except Error (Option Value) := match state.slots binding with
    | none => .ok (state.bindings binding)
    | some slot =>
      match state.heap[slot.address]? with
      | none => .error (.danglingAddress slot.address)
      | some ⟨.binding v, _⟩ => .ok v
      | some _ => .error (.wrongCellKind slot.address)
  match value with
  | .ok (some v) => .ok v
  | .ok none => .error (.uninitialized binding)
  | .error error => .error error

def State.read (state : State) : Ref → Outcome Value
  | .predeclared value => .ok (.scalar value) state
  | .bound binding =>
    match state.bindingValue binding with
    | .ok value => .ok value state
    | .error error => .error error state

def State.write (state : State) (binding : Binding) (value : Value) : State :=
  match state.slots binding with
  | none => { state with bindings := fun key => if key = binding then some value else state.bindings key }
  | some (.captured _ _) => state
  | some (.owned address) =>
    match state.heap[address]? with
    | some ⟨.binding _, frozen⟩ =>
      { state with heap := state.heap.setIfInBounds address ⟨.binding (some value), frozen⟩ }
    | _ => state

/-- Install an initially unbound lexical slot in the current activation. -/
def State.allocateSlot (state : State) (binding : Binding) : State :=
  let address := state.heap.size
  { state with
    heap := state.heap.push ⟨.binding none, false⟩
    slots := fun key => if key = binding then some (.owned address) else state.slots key }

def bindValue (binding : Binding) (value : Value) : Meaning Unit := fun state =>
  .ok () (state.write binding value)

def allocate (elements : List Value) : Meaning Value := fun state =>
  .ok (.list state.heap.size) { state with heap := state.heap.push ⟨.list elements, false⟩ }

def getCell (address : Address) : Meaning Cell := fun state =>
  match state.heap[address]? with
  | some cell => .ok cell state
  | none => .error (.danglingAddress address) state

def projectCell {α : Type} (address : Address) (project : Contents → Option α) : Meaning α := do
  let cell ← getCell address
  match project cell.contents with
  | some result => pure result
  | none => throw (.wrongCellKind address)

def listElements (address : Address) : Meaning (List Value) :=
  projectCell address fun
    | .list elements => some elements
    | _ => none

def tupleElements (address : Address) : Meaning (List Value) :=
  projectCell address fun
    | .tuple elements _ => some elements
    | _ => none

def dictEntries (address : Address) : Meaning (List Entry) :=
  projectCell address fun
    | .dict entries => some entries
    | _ => none

/-- Mutable container keys are disallowed, including when frozen. A tuple's
cached key is computed from its fields at construction. -/
def State.keyOf (state : State) (value : Value) : Except Error Key :=
  match value with
  | .scalar scalar => .ok [.scalar scalar]
  | .tuple address =>
    match state.heap[address]? with
    | none => .error (.danglingAddress address)
    | some ⟨.tuple _ (some key), _⟩ => .ok key
    | some ⟨.tuple _ none, _⟩ => .error (.unhashableKey value)
    | some _ => .error (.wrongCellKind address)
  | .list _ | .dict _ => .error (.unhashableKey value)
  | .function address => .ok [.function address]
  | .builtin id => .ok [.builtin id]
  | .string text => .ok [.string text]

def allocateTuple (elements : List Value) : Meaning Value := fun state =>
  let key := (elements.mapM fun value => (state.keyOf value).toOption).map
    fun parts => .openTuple :: parts.flatten ++ [.closeTuple]
  .ok (.tuple state.heap.size) { state with heap := state.heap.push ⟨.tuple elements key, false⟩ }

def allocateDict (entries : List Entry) : Meaning Value := fun state =>
  .ok (.dict state.heap.size) { state with heap := state.heap.push ⟨.dict entries, false⟩ }

def findEntry (key : Key) (entries : List Entry) : Option Entry :=
  entries.find? fun entry => entry.keyCode == key

/-- Replace only the value of an existing key, retaining its position and original key. -/
def putEntry (entry : Entry) : List Entry → List Entry
  | [] => [entry]
  | old :: rest =>
    if old.keyCode == entry.keyCode then { old with value := entry.value } :: rest
    else old :: putEntry entry rest

/-- Display entries are checked after both operands evaluate and before the next pair. -/
def addDisplayEntry (entries : List Entry) (key value : Value) : Meaning (List Entry) :=
  fun state =>
    match state.keyOf key with
    | .error error => .error error state
    | .ok keyCode =>
      if (findEntry keyCode entries).isSome then .error (.duplicateKey key) state
      else .ok (entries ++ [⟨key, keyCode, value⟩]) state

/-- List indexes range from `-length` through `length - 1`. -/
def normalizeIndex (length : Nat) : Value → Except Error (Fin length)
  | .scalar (.int index) =>
    let offset := if index < 0 then (length : Int) + index else index
    if h : 0 ≤ offset ∧ offset.toNat < length then .ok ⟨offset.toNat, h.2⟩
    else .error (.indexRange index length)
  | _ => .error .indexType

def fromExcept {α : Type} : Except Error α → Meaning α
  | .ok value => pure value
  | .error error => throw error

def readSequence (elements : List Value) (index : Value) : Meaning Value := do
  let i ← fromExcept (normalizeIndex elements.length index)
  pure (elements[i.val]'(i.isLt))

def readDict (address : Address) (key : Value) : Meaning Value := do
  let entries ← dictEntries address
  fun state =>
    match state.keyOf key with
    | .error error => .error error state
    | .ok keyCode =>
      match findEntry keyCode entries with
      | some entry => .ok entry.value state
      | none => .error (.missingKey key) state

def readIndex (receiver index : Value) : Meaning Value :=
  match receiver with
  | .scalar _ | .function _ | .builtin _ | .string _ => throw .indexTarget
  | .list address => listElements address >>= fun elements => readSequence elements index
  | .tuple address => tupleElements address >>= fun elements => readSequence elements index
  | .dict address => readDict address index

/-- Check mutability before applying a same-kind edit to the current cell. -/
def editCell (address : Address) (edit : Contents → Except Error Contents) : Meaning Unit := do
  let cell ← getCell address
  fun state =>
    if cell.frozen then .error (.frozen address) state
    else if state.iterators.contains address then .error (.activeIteration address) state
    else
      match edit cell.contents with
      | .error error => .error error state
      | .ok contents =>
        if cell.contents.sameMutableKind contents then
          .ok () { state with heap := state.heap.setIfInBounds address { cell with contents } }
        else .error (.wrongCellKind address) state

/-- List edits validate their operands before the mutable-cell write. -/
def updateCell (address : Address) (edit : List Value → Except Error (List Value)) :
    Meaning Unit := do
  let elements ← listElements address
  let replacement ← fromExcept (edit elements)
  editCell address fun _ => .ok (.list replacement)

def writeDict (address : Address) (key value : Value) : Meaning Unit :=
  fun state => editCell address (fun
    | .dict entries => do
      let keyCode ← state.keyOf key
      return .dict (putEntry ⟨key, keyCode, value⟩ entries)
    | _ => .error (.wrongCellKind address)) state

def writeIndex (receiver index value : Value) : Meaning Unit :=
  match receiver with
  | .scalar _ | .tuple _ | .function _ | .builtin _ | .string _ => throw .assignmentTarget
  | .list address =>
    updateCell address fun elements => do
      let i ← normalizeIndex elements.length index
      pure (elements.set i.val value)
  | .dict address => writeDict address index value

def appendAt (address : Address) (value : Value) : Meaning Value := do
  updateCell address fun elements => .ok (elements ++ [value])
  return .scalar .none

/-- Resolved syntax indexed by the type of its result. The list element spine,
expressions and statements share a structural recursion principle. -/
inductive Code : Type → Type where
  | scalar (value : Starlark.Value) : Code Value
  | builtin (id : Builtin) : Code Value
  | string (text : String) : Code Value
  | read (ref : Ref) : Code Value
  | list (elements : Code (List Value)) : Code Value
  | tuple (elements : Code (List Value)) : Code Value
  | dict (entries : Code (List Entry)) : Code Value
  | noEntries : Code (List Entry)
  /-- The earlier runs first, then this key and value. -/
  | entry (earlier : Code (List Entry)) (key value : Code Value) : Code (List Entry)
  | empty : Code (List Value)
  | cons (head : Code Value) (tail : Code (List Value)) : Code (List Value)
  | index (receiver index : Code Value) : Code Value
  | append (receiver argument : Code Value) : Code Value
  | pass : Code Unit
  | eval (expr : Code Value) : Code Unit
  | assign (binding : Binding) (rhs : Code Value) : Code Unit
  | setIndex (receiver index rhs : Code Value) : Code Unit
  | seq (first rest : Code Unit) : Code Unit

abbrev Expr := Code Value
abbrev Stmt := Code Unit

end Silmaril.Languages.Starlark.Lists
