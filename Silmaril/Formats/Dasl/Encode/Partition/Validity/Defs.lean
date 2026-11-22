module

public import Silmaril.Formats.Dasl.Encode.Partition.Thms
public import Silmaril.Formats.Dasl.Wire.Profile.Thms
public import Silmaril.Formats.Cbor.Drisl.Cid.Thms

@[expose] public section

namespace Silmaril.Formats.Dasl.Encode.Partition

open Silmaril.Semantics Naming

variable {Name Root Repr : Type} [LinearOrder Name]

def Exact (labels : OrderedMap Name Name) (spec : PER Name) : Prop := PER.fibers labels.lookup? = spec

def Sound (labels : OrderedMap Name Name) (spec : PER Name) : Prop := PER.fibers labels.lookup? ≤ spec

def SameSupport (labels : OrderedMap Name Name) (spec : PER Name) : Prop :=
  ∀ name, name ∈ labels.keySet ↔ spec.Dom name

/-- Evidence consists of a successful decode and an explicit relation on the
decoded map; parse failure does not contribute an empty partition. -/
def Valid (accepts : OrderedMap Name Name → Prop) (codec : PartialCodec (OrderedMap Name Name) Repr)
    (repr : Repr) : Prop := ∃ labels, codec.decode? repr = some labels ∧ accepts labels

/-- Name a representation in an abstract relation, independent of a wire format. -/
def NamedEncodingValid (accepts : OrderedMap Name Name → Prop) (codec : PartialCodec (OrderedMap Name Name) Repr)
    (names : Relation Root Repr) (root : Root) : Prop := ∃ repr, names root repr ∧ Valid accepts codec repr

abbrev nameMap (name : TotalCodec Name (Shallow Root)) : TotalCodec (OrderedMap Name Name) (Shallow Root) :=
  representativeMap name

/-- A name codec for a selected CID envelope. This parses/render names as
base32 text, not as links, and neither hashes nor resolves their payloads. -/
def cidName {WireName : Type} (envelope : Cbor.Drisl.CidProfile) :
    TotalCodec (Cbor.Drisl.Cid envelope) (Shallow WireName) :=
  let adapter := Cbor.Drisl.Cid.codec envelope
  (TotalCodec.mk adapter.render adapter.read?
    (Cbor.Drisl.CidCodec.read_render adapter (Cbor.Drisl.Cid.parse_bytes envelope))).then text

/-- Names and map keys can be different types. The root is an eligible
object name, and its stored bytes must decode under the selected profiles. -/
def namedMaps (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    (store : Relation Root ByteArray) : Relation Root (OrderedMap Name Name) :=
  fun root labels => profile.objectName root = true ∧ project store (profile.decode? (nameMap name)) root labels

def NamedValid (accepts : OrderedMap Name Name → Prop)
    (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    (store : Relation Root ByteArray) (root : Root) : Prop :=
  ∃ labels, namedMaps profile name store root labels ∧ accepts labels

inductive Observation (Map : Type) where
  | unknown
  | rejected
  | decoded (map : Map)

/-- Missing reads are unknown, not rejected. A rejection reports only an
ineligible root or present bytes rejected by this profile. -/
def observeNamed (profile : Wire.Profile Root) (name : TotalCodec Name (Shallow Root))
    (read : Root → Option ByteArray) (root : Root) : Observation (OrderedMap Name Name) :=
  if profile.objectName root then
    match read root with
    | none => .unknown
    | some bytes => match profile.decode? (nameMap name) bytes with
      | none => .rejected
      | some labels => .decoded labels
  else .rejected

/-- Reindex the name side of a relation; this is not a map-key equivalence or
a promise about how a wire profile re-encodes the payload. -/
def rekeyNames (rename : Name → Root) (store : Relation Name Repr) : Relation Root Repr :=
  fun new payload => ∃ old, rename old = new ∧ store old payload

end Silmaril.Formats.Dasl.Encode.Partition
