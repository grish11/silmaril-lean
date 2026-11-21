module

public import Silmaril.Encoding.Relation
public import Silmaril.Formats.Dasl.Defs
public import Mathlib.Data.List.OfFn

@[expose] public section

namespace Silmaril.Formats.Dasl.Encode

open Silmaril.Semantics.Naming

variable {Source Mid Target Name Ref : Type}

/-- Failure to encode is explicit. Decoders may accept additional spellings. -/
structure PartialCodec (Source Target : Type) where
  encode? : Source → Option Target
  decode? : Target → Option Source
  recovers : ∀ ⦃source target⦄, encode? source = some target → decode? target = some source

structure TotalCodec (Source Target : Type) where
  encode : Source → Target
  decode? : Target → Option Source
  recovers : ∀ source, decode? (encode source) = some source

def TotalCodec.partial (codec : TotalCodec Source Target) : PartialCodec Source Target where
  encode? source := some (codec.encode source)
  decode? := codec.decode?
  recovers _ _ hit := (Option.some.inj hit) ▸ codec.recovers _

def PartialCodec.rel (codec : PartialCodec Source Target) : EncRel Target Source :=
  fun repr source => codec.encode? source = some repr

def PartialCodec.then (first : PartialCodec Source Mid) (second : PartialCodec Mid Target) :
    PartialCodec Source Target where
  encode? source := (first.encode? source).bind second.encode?
  decode? target := (second.decode? target).bind first.decode?
  recovers _ _ hit := by
    obtain ⟨_, left, right⟩ := Option.bind_eq_some_iff.mp hit
    exact Option.bind_eq_some_iff.mpr ⟨_, second.recovers right, first.recovers left⟩

def TotalCodec.then (first : TotalCodec Source Mid) (second : TotalCodec Mid Target) :
    TotalCodec Source Target where
  encode source := second.encode (first.encode source)
  decode? target := (second.decode? target).bind first.decode?
  recovers source := Option.bind_eq_some_iff.mpr ⟨_, second.recovers _, first.recovers source⟩

def TotalCodec.prod {Left Right : Type} (left : TotalCodec Source Left) (right : TotalCodec Target Right) :
    TotalCodec (Source × Target) (Left × Right) where
  encode pair := (left.encode pair.1, right.encode pair.2)
  decode? pair := do pure (← left.decode? pair.1, ← right.decode? pair.2)
  recovers pair := by simp [left.recovers, right.recovers]

/-- Opt-in defaults; callers can always pass a different codec. -/
class DefaultCodec (Source Target : Type) where
  codec : TotalCodec Source Target

def defaultCodec (Source Target : Type) [DefaultCodec Source Target] : TotalCodec Source Target :=
  DefaultCodec.codec

def bits : TotalCodec UInt64 (Tree Ref Name) := ⟨Tree.i64, (fun | .i64 value => some value | _ => none), fun _ => rfl⟩

def signed : TotalCodec Int64 (Tree Ref Name) :=
  ⟨(fun value => .i64 value.toUInt64), (fun | .i64 value => some value.toInt64 | _ => none), fun value => by simp⟩

def bytes : TotalCodec ByteArray (Tree Ref Name) :=
  ⟨Tree.bytes, (fun | .bytes value => some value | _ => none), fun _ => rfl⟩

def text : TotalCodec String (Tree Ref Name) :=
  ⟨Tree.string, (fun | .string value => some value | _ => none), fun _ => rfl⟩

def boolean : TotalCodec Bool (Tree Ref Name) :=
  ⟨Tree.bool, (fun | .bool value => some value | _ => none), fun _ => rfl⟩

def null : TotalCodec Unit (Tree Ref Name) :=
  ⟨(fun _ => .null), (fun | .null => some () | _ => none), fun ⟨⟩ => rfl⟩

def link : TotalCodec (Link Name) (Shallow Name) :=
  ⟨Tree.ref, (fun | .ref value => some value | _ => none), fun _ => rfl⟩

structure Blob where
  payload : ByteArray

def blob : TotalCodec Blob Value :=
  ⟨(fun value => Value.blob value.payload), (fun | Tree.blob _ value => some ⟨value⟩ | _ => none), fun ⟨_⟩ => rfl⟩

instance : DefaultCodec UInt64 (Tree Ref Name) := ⟨bits⟩
instance : DefaultCodec Int64 (Tree Ref Name) := ⟨signed⟩
instance : DefaultCodec ByteArray (Tree Ref Name) := ⟨bytes⟩
instance : DefaultCodec String (Tree Ref Name) := ⟨text⟩
instance : DefaultCodec Bool (Tree Ref Name) := ⟨boolean⟩
instance : DefaultCodec Unit (Tree Ref Name) := ⟨null⟩
instance : DefaultCodec (Link Name) (Shallow Name) := ⟨link⟩
instance : DefaultCodec Blob Value := ⟨blob⟩

structure Fields (Item : Type) where
  keys : Finset String
  values : ↥keys → Item

def Fields.map (fields : Fields Source) (encode : Source → Target) : Fields Target :=
  ⟨fields.keys, encode ∘ fields.values⟩

def Fields.traverse? (fields : Fields Source) (convert : Source → Option Target) : Option (Fields Target) :=
  if present : ∀ key (member : key ∈ fields.keys), (convert (fields.values ⟨key, member⟩)).isSome = true then
    some ⟨fields.keys, fun key => (convert (fields.values key)).get (present key.val key.property)⟩
  else none

def dict : TotalCodec (Fields (Tree Ref Name)) (Tree Ref Name) :=
  ⟨(fun fields => .dict fields.keys fields.values), (fun | .dict keys values => some ⟨keys, values⟩ | _ => none),
    fun ⟨_, _⟩ => rfl⟩

def list : TotalCodec (List (Tree Ref Name)) (Tree Ref Name) :=
  ⟨(fun items => .list items.length items.get), (fun | .list _ children => some (List.ofFn children) | _ => none),
    fun items => congrArg some (List.ofFn_get items)⟩

def PartialCodec.listEncode (codec : PartialCodec Source Target) (items : List Source) : Option (List Target) :=
  items.mapM codec.encode?

def PartialCodec.listDecode (codec : PartialCodec Source Target) (items : List Target) : Option (List Source) :=
  items.mapM codec.decode?

def TotalCodec.listEncode (codec : TotalCodec Source Target) (items : List Source) : List Target :=
  items.map codec.encode

/-- Interpret only the representations produced by the selected encoder, not all the
spellings a decoder happens to accept. -/
def codedNames (raw : Relation Name Target) (codec : PartialCodec Source Target) : Relation Name Source :=
  push raw codec.rel

end Silmaril.Formats.Dasl.Encode
