module

public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Lex
public import Silmaril.Formats.Dasl.Encode.Map.Thms
public import Silmaril.Formats.Dasl.Wire.Profile.Defs

@[expose] public section

namespace Silmaril.Formats.Dasl.LinkedSet

open Silmaril.Semantics (OrderedMap)

variable {Object Name : Type}

inductive Item (Object : Type) where
  | object (value : Object)
  | blob (bytes : ByteArray)

/-- Full bytes in unsigned lexicographic order, not a digest. The first octet
separates objects from blobs. -/
abbrev Key := List (Fin 256)

def octets (bytes : ByteArray) : Key := bytes.data.toList.map UInt8.toFin

def key? (objects : Encode.PartialCodec Object ByteArray) : Item Object → Option Key
  | .object value => (objects.encode? value).map (fun bytes => 0 :: octets bytes)
  | .blob bytes => some (1 :: octets bytes)

structure Reader (Object Name : Type) where
  object? : Name → Option Object
  blob? : Name → Option ByteArray

def Reader.resolve? (reader : Reader Object Name) : Link Name → Option (Item Object)
  | .obj name => (reader.object? name).map Item.object
  | .blob name => (reader.blob? name).map Item.blob

/-- The wire grammar for object bodies, root-kind eligibility, and selected
name policy are different inputs. A blob has no object parser. -/
def Reader.wire (profile : Wire.Profile Name) (layout : Encode.TotalCodec Object (Shallow Name))
    (blobName : Name → Bool) (read : Name → Option ByteArray) : Reader Object Name :=
  ⟨profile.read? layout read, fun name => if blobName name then read name else none⟩

structure Profile (Object Name : Type) where
  objects : Encode.PartialCodec Object ByteArray
  reader : Reader Object Name
  preferred : Key → Option (Link Name)

abbrev Layout (Name : Type) := OrderedMap Key (Link Name)

def Profile.entry? [DecidableEq Name] (profile : Profile Object Name) (link : Link Name) :
    Option (Key × Link Name) :=
  (profile.reader.resolve? link).bind fun value => (key? profile.objects value).bind fun key =>
    if profile.preferred key = some link then some (key, link) else none

def Profile.entryForKey? [DecidableEq Name] (profile : Profile Object Name) (key : Key) :
    Option (Key × Link Name) :=
  (profile.preferred key).bind fun link => (profile.entry? link).bind fun (actual, _) =>
    if actual = key then some (key, link) else none

def Valid [DecidableEq Name] (profile : Profile Object Name) (layout : Layout Name) : Prop :=
  ∀ entry ∈ layout.entries, profile.entry? entry.2 = some entry

def Supported [DecidableEq Name] (profile : Profile Object Name) (key : Key) : Prop :=
  ∃ entry, profile.entryForKey? key = some entry

def Member (profile : Profile Object Name) (layout : Layout Name) (value : Item Object) : Prop :=
  ∃ key ∈ layout.keys, key? profile.objects value = some key

def cardinality (layout : Layout Name) : Nat := layout.entries.length

def keys (layout : Layout Name) : Finset Key := layout.keys.toFinset

def ofKeys? [DecidableEq Name] (profile : Profile Object Name) (keys : Finset Key) : Option (Layout Name) :=
  (keys.sort.mapM profile.entryForKey?).bind OrderedMap.ofEntries?

def normalize? [DecidableEq Name] (profile : Profile Object Name) (values : List (Item Object)) :
    Option (Layout Name) :=
  (values.mapM (key? profile.objects)).bind (fun keys => ofKeys? profile keys.toFinset)

def linkList : Encode.TotalCodec (List (Link Name)) (Shallow Name) := Encode.listOf Encode.link

def encode (layout : Layout Name) : Shallow Name := linkList.encode (layout.entries.map Prod.snd)

/-- Read all linked payloads, recompute keys, enforce the selected links, then
validate strict semantic key order. No validity is inferred from the block's
list order or from the names alone. -/
def decode? [DecidableEq Name] (profile : Profile Object Name) (value : Shallow Name) : Option (Layout Name) :=
  (linkList.decode? value).bind fun links => (links.mapM profile.entry?).bind OrderedMap.ofEntries?

end Silmaril.Formats.Dasl.LinkedSet
