module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Order.Sum.Order
public import Silmaril.Formats.Dasl.Encode.Map.Thms
public import Silmaril.Formats.Dasl.Wire.Profile.Defs
import all Silmaril.Formats.Dasl.Encode.Map.Thms
import all Silmaril.Formats.Dasl.Encode.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.NameLinkSet

open Silmaril.Semantics

variable {Key Name Value : Type}

abbrev Layout (Key : Type) [LinearOrder Key] := OrderedSet Key

/-- Objects sort before blobs. Within either kind only the selected name order matters. -/
abbrev MixedKey (Name : Type) := Name ⊕ₗ Name

def objectKey : Encode.TotalCodec Name (Link Name) :=
  ⟨Link.obj, (fun | .obj name => some name | .blob _ => none), fun _ => rfl⟩

def blobKey : Encode.TotalCodec Name (Link Name) :=
  ⟨Link.blob, (fun | .blob name => some name | .obj _ => none), fun _ => rfl⟩

def taggedKey : Link Name → MixedKey Name
  | .obj name => toLex (.inl name)
  | .blob name => toLex (.inr name)

def mixedKey : Encode.TotalCodec (MixedKey Name) (Link Name) :=
  ⟨(fun key => match ofLex key with | .inl name => .obj name | .inr name => .blob name),
    some ∘ taggedKey, fun key => by cases key <;> rfl⟩

abbrev cidOrder {format : Cbor.Drisl.CidProfile} : LinearOrder (Cbor.Drisl.Cid format) :=
  LinearOrder.lift' (fun cid => cid.val.map UInt8.toFin) (fun _ _ same =>
    Subtype.ext (List.map_injective_iff.mpr (fun _ _ hit => UInt8.toFin_inj.mp hit) same))

variable [LinearOrder Key]

def ofFinset (names : Finset Key) : Layout Key :=
  ⟨names.sort.map (·, ()), List.pairwise_map.mpr (Finset.sortedLT_sort names).pairwise⟩

def normalize (names : List Key) : Layout Key := ofFinset names.toFinset

def links (key : Encode.TotalCodec Key (Link Name)) (layout : Layout Key) : List (Link Name) :=
  layout.keys.map key.encode

def linkArray : Encode.TotalCodec (List (Link Name)) (Shallow Name) := Encode.listOf Encode.link

/-- Decode strictly increasing keys without consulting a payload store. A permissive
key decoder may not substitute a different link identity. -/
def codec [DecidableEq Name] (key : Encode.TotalCodec Key (Link Name)) : Encode.TotalCodec (Layout Key) (Shallow Name) :=
  let base := Encode.setKeys.then key.listCodec
  ⟨(fun set => linkArray.encode (links key set)), (fun repr => do
    let actual ← linkArray.decode? repr
    let set ← base.decode? actual
    if actual = links key set then some set else none), fun set => by
      have recovered : base.decode? (links key set) = some set := base.recovers set
      simp [linkArray.recovers, recovered]⟩

def objectCodec [LinearOrder Name] : Encode.TotalCodec (Layout Name) (Shallow Name) := codec objectKey

def blobCodec [LinearOrder Name] : Encode.TotalCodec (Layout Name) (Shallow Name) := codec blobKey

def mixedCodec [LinearOrder Name] : Encode.TotalCodec (Layout (MixedKey Name)) (Shallow Name) := codec mixedKey

def supported (key : Encode.TotalCodec Key (Link Name)) (accept : Link Name → Bool) (set : Layout Key) : Bool :=
  set.keys.all (accept ∘ key.encode)

/-- Kind admission is independent of the wire parser, name order and address selection.
For the concrete CID profiles use `Wire.linkSupported`; its object and blob cases are disjoint. -/
def wireCodec [DecidableEq Name] (profile : Wire.Profile Name) (accept : Link Name → Bool)
    (key : Encode.TotalCodec Key (Link Name)) : Encode.PartialCodec (Layout Key) ByteArray :=
  letI : DecidableEq (Layout Key) := fun left right =>
    decidable_of_iff (left.entries = right.entries) ⟨OrderedMap.ext, congrArg OrderedMap.entries⟩
  let wire := profile.codec (codec key)
  let retain := fun set => if supported key accept set then some set else none
  ⟨(fun set => if supported key accept set then wire.encode? set else none),
    (fun bytes => (wire.decode? bytes).bind retain), fun {set bytes} hit => by
      split at hit
      · rw [wire.recovers hit]
        simp [retain, ‹supported key accept set = true›]
      · cases hit⟩

def cidWireCodec {format : Cbor.Drisl.CidProfile} (profile : Wire.Profile (Cbor.Drisl.Cid format))
    (key : Encode.TotalCodec Key (Link (Cbor.Drisl.Cid format))) : Encode.PartialCodec (Layout Key) ByteArray :=
  wireCodec profile Wire.linkSupported key

def names (set : Layout Key) : Finset Key := set.keys.toFinset

def cardinality (set : Layout Key) : Nat := set.keys.length

def contents (key : Encode.TotalCodec Key (Link Name)) (rel : Naming.Relation (Link Name) Value)
    (set : Layout Key) : Set Value :=
  { value | ∃ name ∈ names set, rel (key.encode name) value }

/-- The caller chooses a total selector; only choices on the requested set need a binding. -/
def Coherent (key : Encode.TotalCodec Key (Link Name)) (rel : Naming.Relation (Link Name) Value)
    (chooseName : Value → Key) (values : Finset Value) : Prop :=
  ∀ value ∈ values, rel (key.encode (chooseName value)) value

def ofContents (chooseName : Value → Key) (values : Finset Value) : Layout Key := ofFinset (values.image chooseName)

/-- A reusable in-memory index. Its sorted array is built once from the wire layout. -/
structure Index (Key : Type) [LinearOrder Key] where
  names : Array Key
  ordered : names.toList.Pairwise (· < ·)

def index (set : Layout Key) : Index Key :=
  ⟨set.keys.toArray, by simpa [OrderedMap.keys] using List.pairwise_map.mpr set.ordered⟩

/-- Binary search a half-open window; when the pivot misses, discard it and one side. -/
def search (names : Array Key) (query : Key) (start width : Nat) (fits : start + width ≤ names.size) : Bool :=
  if nonempty : 0 < width then
    let pivot := start + width / 2
    let there := names[pivot]'(by dsimp [pivot]; omega)
    if query < there then search names query start (width / 2) (by omega)
    else if there < query then search names query (pivot + 1) (width - width / 2 - 1) (by dsimp [pivot]; omega)
    else true
  else false
termination_by width
decreasing_by all_goals omega

def Index.contains (idx : Index Key) (query : Key) : Bool := search idx.names query 0 idx.names.size (by simp)

inductive Resolution (Value : Type) where
  | unresolved
  | missing
  | invalid
  | found (value : Value)
  deriving DecidableEq

/-- `none` is absence from the index, not a statement about the store. -/
def Index.lookup (idx : Index Key) (key : Encode.TotalCodec Key (Link Name))
    (read : Link Name → Resolution Value) (query : Key) : Option (Resolution Value) :=
  if idx.contains query then some (read (key.encode query)) else none

def Sound (read : Link Name → Resolution Value) (rel : Naming.Relation (Link Name) Value) : Prop :=
  ∀ ⦃link value⦄, read link = .found value → rel link value

variable {Object : Type}

def decodeTarget? (profile : Wire.Profile Name) (objects : Encode.TotalCodec Object (Shallow Name))
    (link : Link Name) (bytes : ByteArray) : Option (Object ⊕ ByteArray) :=
  match link with
  | .obj _ => (profile.decode? objects bytes).map Sum.inl
  | .blob _ => some (.inr bytes)

def targetName : Link Name → Name
  | .obj name | .blob name => name

/-- Admitted targets whose stored bytes decode as the indicated kind. -/
def decodedBindings (profile : Wire.Profile Name) (accept : Link Name → Bool)
    (objects : Encode.TotalCodec Object (Shallow Name)) (store : Naming.Relation Name ByteArray) :
    Naming.Relation (Link Name) (Object ⊕ ByteArray) :=
  fun link value => accept link = true ∧
    ∃ bytes, store (targetName link) bytes ∧ decodeTarget? profile objects link bytes = some value

/-- Wrong kinds and ill-formed objects are invalid. Raw blob bytes are not parsed as objects. -/
def wireReader (profile : Wire.Profile Name) (accept : Link Name → Bool)
    (objects : Encode.TotalCodec Object (Shallow Name)) (read : Name → Option ByteArray)
    (link : Link Name) : Resolution (Object ⊕ ByteArray) :=
  if accept link then
    match read (targetName link) with
    | none => .missing
    | some bytes => match decodeTarget? profile objects link bytes with
      | none => .invalid
      | some value => .found value
  else .invalid

end Silmaril.Formats.Dasl.NameLinkSet
