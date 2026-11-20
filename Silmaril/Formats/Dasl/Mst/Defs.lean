module

public import Mathlib.Data.List.Lex
public import Silmaril.Formats.Dasl.Encode.Thms
public import Silmaril.Formats.Dasl.Wire.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.Mst

abbrev Key := List UInt8

variable {Name : Type}

structure Entry (Name : Type) where
  key : Key
  record : Name
  right : Option Name
  deriving DecidableEq, Repr

structure Node (Name : Type) where
  left : Option Name
  entries : List (Entry Name)
  deriving DecidableEq, Repr

structure WireEntry (Name : Type) where
  shared : Nat
  suffix : Key
  record : Name
  right : Option Name
  deriving DecidableEq, Repr

structure WireNode (Name : Type) where
  left : Option Name
  entries : List (WireEntry Name)
  deriving DecidableEq, Repr

def Key.before (left right : Key) : Prop := left.map UInt8.toFin < right.map UInt8.toFin

instance (left right : Key) : Decidable (left.before right) :=
  inferInstanceAs (Decidable (left.map UInt8.toFin < right.map UInt8.toFin))

def prefixLength : Key → Key → Nat
  | first :: left, next :: right => if first = next then prefixLength left right + 1 else 0
  | _, _ => 0

def compressEntries (previous : Key) : List (Entry Name) → List (WireEntry Name)
  | [] => []
  | entry :: tail =>
    let shared := prefixLength previous entry.key
    ⟨shared, entry.key.drop shared, entry.record, entry.right⟩ :: compressEntries entry.key tail

/-- Recompute the prefix to reject overlong and non-maximal prefix claims. -/
def expandEntries? (previous : Key) : List (WireEntry Name) → Option (List (Entry Name))
  | [] => some []
  | entry :: tail => do
    let key := previous.take entry.shared ++ entry.suffix
    if prefixLength previous key = entry.shared then
      let remaining ← expandEntries? key tail
      pure (⟨key, entry.record, entry.right⟩ :: remaining)
    else none

def Node.compress (node : Node Name) : WireNode Name := ⟨node.left, compressEntries [] node.entries⟩

def WireNode.expand? (node : WireNode Name) : Option (Node Name) :=
  (expandEntries? [] node.entries).map (Node.mk node.left)

def entryFields : Finset String := {"k", "p", "t", "v"}
def nodeFields : Finset String := {"e", "l"}

def encodeChild : Option Name → Shallow Name
  | none => .null
  | some name => .ref (.obj name)

def decodeChild : Shallow Name → Option (Option Name)
  | .null => some none
  | .ref (.obj name) => some (some name)
  | _ => none

def decodeRecord : Shallow Name → Option Name
  | .ref (.obj name) => some name
  | _ => none

def encodeWireEntry? (entry : WireEntry Name) : Option (Shallow Name) :=
  if entry.shared < 2^63 then
    some (.dict entryFields fun key =>
      match key.val with
      | "k" => .bytes entry.suffix.toByteArray
      | "p" => .i64 (UInt64.ofNat entry.shared)
      | "t" => encodeChild entry.right
      | _ => .ref (.obj entry.record))
  else none

def decodeWireEntry? : Shallow Name → Option (WireEntry Name)
  | .dict keys values => do
    if same : keys = entryFields then
      let fields : ↥entryFields → Shallow Name := same ▸ values
      let .bytes suffix := fields ⟨"k", by decide⟩ | none
      let .i64 shared := fields ⟨"p", by decide⟩ | none
      if shared.toNat < 2^63 then
        let right ← decodeChild (fields ⟨"t", by decide⟩)
        let record ← decodeRecord (fields ⟨"v", by decide⟩)
        pure ⟨shared.toNat, suffix.data.toList, record, right⟩
      else none
    else none
  | _ => none

def encodeWireNode? (node : WireNode Name) : Option (Shallow Name) := do
  let entries ← node.entries.mapM encodeWireEntry?
  pure (.dict nodeFields fun key => if key.val = "e" then Encode.list.encode entries else encodeChild node.left)

def decodeWireNode? : Shallow Name → Option (WireNode Name)
  | .dict keys values => do
    if same : keys = nodeFields then
      let fields : ↥nodeFields → Shallow Name := same ▸ values
      let left ← decodeChild (fields ⟨"l", by decide⟩)
      let entries ← Encode.list.decode? (fields ⟨"e", by decide⟩)
      pure ⟨left, ← entries.mapM decodeWireEntry?⟩
    else none
  | _ => none

def encodeNode? (node : Node Name) : Option (Shallow Name) := encodeWireNode? node.compress
def decodeNode? (value : Shallow Name) : Option (Node Name) := (decodeWireNode? value).bind WireNode.expand?

/-- The partial node relation induced by a shallow object reference. -/
def nodes (objects : Semantics.Naming.Relation Name (Shallow Name)) : Semantics.Naming.Relation Name (Node Name) :=
  Semantics.Naming.push objects (Semantics.Naming.graph decodeNode?)

structure Context where
  layer : Nat
  lower : Option Key := none
  upper : Option Key := none
  root : Bool := false

def Context.acceptsKey (ctx : Context) (layerOf : Key → Nat) (key : Key) : Prop :=
  key.isEmpty = false ∧ layerOf key = ctx.layer ∧
  (∀ lower ∈ ctx.lower, Key.before lower key) ∧ (∀ upper ∈ ctx.upper, Key.before key upper)

instance (ctx : Context) (layerOf : Key → Nat) (key : Key) : Decidable (ctx.acceptsKey layerOf key) := by
  unfold Context.acceptsKey
  cases ctx.lower <;> cases ctx.upper <;> simp <;> infer_instance

/-- Empty internal nodes must have a child; the empty root has layer zero and
no children. Nonempty nodes at layer zero may not have children. -/
def Context.Valid (ctx : Context) (layerOf : Key → Nat) (node : Node Name) : Prop :=
  node.entries.Pairwise (fun left right => left.key.before right.key) ∧
  (∀ entry ∈ node.entries, ctx.acceptsKey layerOf entry.key ∧ (ctx.layer = 0 → entry.right.isNone = true)) ∧
  (ctx.layer = 0 → node.left.isNone = true) ∧
  (node.entries.isEmpty = true →
    if ctx.root then ctx.layer = 0 ∧ node.left.isNone = true else node.left.isSome = true)

instance (ctx : Context) (layerOf : Key → Nat) (node : Node Name) : Decidable (ctx.Valid layerOf node) := by
  unfold Context.Valid
  infer_instance

def Node.rootContext (node : Node Name) (layerOf : Key → Nat) : Context :=
  ⟨(node.entries.head?.map (layerOf ∘ Entry.key)).getD 0, none, none, true⟩

inductive Read (Name : Type) (Valid : Node Name → Prop) where
  | missing
  | invalidWire
  | invalidNode
  | found (node : Node Name) (checked : Valid node)

def readChecked {valid : Node Name → Prop} [DecidablePred valid] : Wire.ReadResult (Shallow Name) → Read Name valid
  | .missing => .missing
  | .invalidWire => .invalidWire
  | .found value => match decodeNode? value with
    | none => .invalidNode
    | some node => if checked : valid node then .found node checked else .invalidNode

def readAt (layerOf : Key → Nat) (ctx : Context) : Wire.ReadResult (Shallow Name) → Read Name (ctx.Valid layerOf) :=
  readChecked

def readRoot (layerOf : Key → Nat) :
    Wire.ReadResult (Shallow Name) → Read Name (fun node => (node.rootContext layerOf).Valid layerOf node) :=
  readChecked

end Silmaril.Formats.Dasl.Mst
