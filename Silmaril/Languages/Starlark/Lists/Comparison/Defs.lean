module

public import Silmaril.Languages.Starlark.Lists.Defs

@[expose] public section

namespace Silmaril.Languages.Starlark.Lists.Comparison

/-- A scan returns the first decisive Boolean or error. Exhaustion returns the
opposite Boolean. -/
def scan {α : Type} (test : α → Except Error Bool) (decisive : Bool) :
    List α → Except Error Bool
  | [] => .ok (!decisive)
  | item :: rest =>
    match test item with
    | .error error => .error error
    | .ok flag => if flag = decisive then .ok flag else scan test decisive rest

/-- The first comparison starts with the pinned Go default. Each paired
field consumes one level. Membership starts a fresh comparison per element. -/
def defaultDepth : Nat := 10

inductive SequenceKind where
  | list | tuple

def SequenceKind.locate : Value → Option (SequenceKind × Address)
  | .list address => some (.list, address)
  | .tuple address => some (.tuple, address)
  | _ => none

inductive MembershipTarget where
  | sequence (kind : SequenceKind) (address : Address)
  | dictionary (address : Address)
  | unsupported

def MembershipTarget.ofValue : Value → MembershipTarget
  | .dict address => .dictionary address
  | value =>
    match SequenceKind.locate value with
    | some (kind, address) => .sequence kind address
    | none => .unsupported

/-- Read the live elements of a reached sequence. Tuple key caches and list
mutation guards are irrelevant to this read. -/
def SequenceKind.elements (kind : SequenceKind) (heap : Heap) (address : Address) : Except Error (List Value) :=
  match kind with
  | .tuple => heap.tupleFields address
  | .list =>
    match heap[address]? with
    | none => .error (.danglingAddress address)
    | some ⟨.list fields, _⟩ => .ok fields
    | some _ => .error (.wrongCellKind address)

/-- Classify the operands by type without reading heap cells. -/
inductive Pair where
  | scalars (left right : Starlark.Value)
  | strings (left right : String)
  | sequences (kind : SequenceKind) (left right : Address)
  | dictionaries (left right : Address)
  | different
  | unsupported

def Pair.ofValues : Value → Value → Pair
  | .scalar a, .scalar b => .scalars a b
  | .string a, .string b => .strings a b
  | .tuple a, .tuple b => .sequences .tuple a b
  | .list a, .list b => .sequences .list a b
  | .dict a, .dict b => .dictionaries a b
  | .scalar _, .string _ | .string _, .scalar _
  | .scalar _, .tuple _ | .tuple _, .scalar _
  | .string _, .tuple _ | .tuple _, .string _ => .different
  | .list _, .scalar _ | .scalar _, .list _
  | .list _, .string _ | .string _, .list _
  | .list _, .tuple _ | .tuple _, .list _ => .different
  | .dict _, .scalar _ | .scalar _, .dict _
  | .dict _, .string _ | .string _, .dict _
  | .dict _, .list _ | .list _, .dict _
  | .dict _, .tuple _ | .tuple _, .dict _ => .different
  | _, _ => .unsupported

/-- The Boolean read by scalar `==`, including exact mixed numeric comparison. -/
def scalarEqual (left right : Starlark.Value) : Bool :=
  match left.orderedCompare right with
  | some order => order == .eq
  | none => left.isNone && right.isNone

/-- Read a live dictionary's entries in insertion order. -/
def dictionaryEntries (heap : Heap) (address : Address) : Except Error (List Entry) :=
  match heap[address]? with
  | none => .error (.danglingAddress address)
  | some ⟨.dict entries, _⟩ => .ok entries
  | some _ => .error (.wrongCellKind address)

/-- Canonical lookup uses the same validation and key-code search as indexing.
A miss has its own result, separate from a reached error. -/
def lookupDictionary (heap : Heap) (address : Address) (key : Value) : Except Error (Option Entry) := do
  let entries ← dictionaryEntries heap address
  let code ← ({ heap := heap } : State).keyOf key
  pure (findEntry code entries)

/-- Search supplied candidates in order, stopping at the first hit or error. -/
def probe {α : Type} (test : α → Except Error Bool) : List α → Except Error (Option α)
  | [] => .ok none
  | candidate :: later =>
    match test candidate with
    | .error error => .error error
    | .ok true => .ok (some candidate)
    | .ok false => probe test later

/-- Go's mapping membership and dictionary equality project a failed lookup
to the same observation as a miss. -/
def lookupOrMiss {α : Type} : Except Error (Option α) → Option α
  | .ok found => found
  | .error _ => none

/-- Each canonical key code names at most one entry of a dictionary table. -/
def UniqueKeyCodes (entries : List Entry) : Prop :=
  entries.Pairwise fun left right => left.keyCode ≠ right.keyCode

/-- Select by the established cached key encoding, then compare the reached
values. An absent key is decisive without evaluating a value pair. -/
def compareEntry (equal : Value → Value → Except Error Bool) (right : List Entry)
    (left : Entry) : Except Error Bool :=
  match findEntry left.keyCode right with
  | none => .ok false
  | some entry => equal left.value entry.value

/-- Both cells are read left to right, even for an address compared with
itself. Length mismatch skips the fields. Budget exhaustion terminates any
reached cycle. -/
def equalAt (heap : Heap) : Nat → Value → Value → Except Error Bool
  | 0, _, _ => .error .comparisonDepth
  | depth + 1, left, right =>
    match Pair.ofValues left right with
    | .scalars a b => .ok (scalarEqual a b)
    | .strings a b => .ok (decide (a = b))
    | .different => .ok false
    | .unsupported => .error (.comparisonType left right)
    | .sequences kind a b => do
      let xs ← kind.elements heap a
      let ys ← kind.elements heap b
      if xs.length = ys.length then
        scan (fun pair => equalAt heap depth pair.1 pair.2) false (xs.zip ys)
      else pure false
    | .dictionaries a b => do
      let xs ← dictionaryEntries heap a
      let ys ← dictionaryEntries heap b
      if xs.length = ys.length then
        scan (compareEntry (equalAt heap depth) ys) false xs
      else pure false

/-- Probe a supplied candidate order with a fresh full comparison per key.
The caller supplies the candidates selected by the table's hash and bucket rules. -/
def probeKeys (heap : Heap) (depth : Nat) (key : Value) (candidates : List Entry) :
    Except Error (Option Entry) :=
  probe (fun entry => equalAt heap depth key entry.key) candidates

/-- Sequences test their elements in order. Dictionaries test key presence
and retain the checked lookup error. -/
def containsAt (heap : Heap) (depth : Nat) (needle target : Value) : Except Error Bool :=
  match MembershipTarget.ofValue target with
  | .sequence kind address => do
    let fields ← kind.elements heap address
    scan (fun field => equalAt heap depth field needle) true fields
  | .dictionary address => Option.isSome <$> lookupDictionary heap address needle
  | .unsupported => .error (.membershipTarget target)

def evaluate (heap : Heap) (op : ComparisonOp) (left right : Value) : Except Error Bool :=
  match op with
  | .eq => equalAt heap defaultDepth left right
  | .ne => (! ·) <$> equalAt heap defaultDepth left right
  | .mem => containsAt heap defaultDepth left right
  | .notMem => (! ·) <$> containsAt heap defaultDepth left right

def finish (out : Except Error Bool) : Meaning Value :=
  fromExcept (out.map fun flag => .scalar (.bool flag))

def apply (op : ComparisonOp) (left right : Value) : Meaning Value := fun state =>
  finish (evaluate state.heap op left right) state

end Silmaril.Languages.Starlark.Lists.Comparison
