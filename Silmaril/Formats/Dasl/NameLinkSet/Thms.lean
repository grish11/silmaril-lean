module

public import Silmaril.Formats.Dasl.NameLinkSet.Defs
import Silmaril.Proofs.Formats.Dasl.NameLinkSet

public section

namespace Silmaril.Formats.Dasl.NameLinkSet

open Silmaril.Semantics

variable {Key Name Value Object : Type} [LinearOrder Key]

def equiv : Layout Key ≃ Finset Key :=
  ⟨names, ofFinset, Proofs.Formats.Dasl.NameLinkSet.ofFinset_names, Proofs.Formats.Dasl.NameLinkSet.names_ofFinset⟩

theorem normalize_names (keys : List Key) : names (normalize keys) = keys.toFinset :=
  equiv.apply_symm_apply keys.toFinset

theorem cardinality_eq (layout : Layout Key) : cardinality layout = (names layout).card :=
  Proofs.Formats.Dasl.NameLinkSet.cardinality_eq layout

theorem recovers [DecidableEq Name] (key : Encode.TotalCodec Key (Link Name)) (layout : Layout Key) :
    (codec key).decode? ((codec key).encode layout) = some layout := (codec key).recovers layout

theorem decode_exact [DecidableEq Name] (key : Encode.TotalCodec Key (Link Name))
    {repr : Shallow Name} {layout : Layout Key} (hit : (codec key).decode? repr = some layout) :
    linkArray.decode? repr = some (links key layout) := Proofs.Formats.Dasl.NameLinkSet.decode_exact key hit

theorem wire_recovers [DecidableEq Name] (profile : Wire.Profile Name) (accept : Link Name → Bool)
    (key : Encode.TotalCodec Key (Link Name)) {layout : Layout Key} {bytes : ByteArray}
    (hit : (wireCodec profile accept key).encode? layout = some bytes) :
    (wireCodec profile accept key).decode? bytes = some layout := (wireCodec profile accept key).recovers hit

theorem wire_decode_supported [DecidableEq Name] (profile : Wire.Profile Name) (accept : Link Name → Bool)
    (key : Encode.TotalCodec Key (Link Name)) {layout : Layout Key} {bytes : ByteArray}
    (hit : (wireCodec profile accept key).decode? bytes = some layout) :
    ∀ name ∈ names layout, accept (key.encode name) = true := by
  have admitted := (Proofs.Formats.Dasl.NameLinkSet.wire_decode_admitted profile accept key hit).2
  simpa [names, supported, List.all_eq_true] using admitted

theorem wire_decode_exact [DecidableEq Name] (profile : Wire.Profile Name) (accept : Link Name → Bool)
    (key : Encode.TotalCodec Key (Link Name)) {layout : Layout Key} {bytes : ByteArray}
    (hit : (wireCodec profile accept key).decode? bytes = some layout) :
    (profile.parse? bytes).bind linkArray.decode? = some (links key layout) := by
  obtain ⟨repr, parsed, decoded⟩ := Option.bind_eq_some_iff.mp
    (Proofs.Formats.Dasl.NameLinkSet.wire_decode_admitted profile accept key hit).1
  exact Option.bind_eq_some_iff.mpr ⟨repr, parsed, decode_exact key decoded⟩

theorem supported_kinds_disjoint {format : Cbor.Drisl.CidProfile} (name : Cbor.Drisl.Cid format)
    (object : Wire.linkSupported (.obj name) = true) : Wire.linkSupported (.blob name) = false :=
  Proofs.Formats.Dasl.NameLinkSet.supported_kinds_disjoint name object

theorem contains_iff (layout : Layout Key) (query : Key) :
    (index layout).contains query = true ↔ query ∈ names layout :=
  Proofs.Formats.Dasl.NameLinkSet.contains_iff layout query

theorem lookup_of_mem (layout : Layout Key) (key : Encode.TotalCodec Key (Link Name))
    (read : Link Name → Resolution Value) {query : Key} (member : query ∈ names layout) :
    (index layout).lookup key read query = some (read (key.encode query)) :=
  Proofs.Formats.Dasl.NameLinkSet.lookup_of_mem layout key read member

theorem lookup_none_iff (layout : Layout Key) (key : Encode.TotalCodec Key (Link Name))
    (read : Link Name → Resolution Value) (query : Key) :
    (index layout).lookup key read query = none ↔ query ∉ names layout :=
  Proofs.Formats.Dasl.NameLinkSet.lookup_none_iff layout key read query

theorem lookup_eq_some_iff (layout : Layout Key) (key : Encode.TotalCodec Key (Link Name))
    (read : Link Name → Resolution Value) (query : Key) (result : Resolution Value) :
    (index layout).lookup key read query = some result ↔
      query ∈ names layout ∧ read (key.encode query) = result :=
  Proofs.Formats.Dasl.NameLinkSet.lookup_eq_some_iff layout key read query result

theorem lookup_found (layout : Layout Key) (key : Encode.TotalCodec Key (Link Name))
    {read : Link Name → Resolution Value} {rel : Naming.Relation (Link Name) Value}
    (sound : Sound read rel) {query : Key} {value : Value}
    (hit : (index layout).lookup key read query = some (.found value)) :
    query ∈ names layout ∧ rel (key.encode query) value := by
  obtain ⟨member, resolution⟩ := (lookup_eq_some_iff layout key read query (.found value)).mp hit
  exact ⟨member, sound resolution⟩

theorem mem_contents_of_lookup_found (layout : Layout Key) (key : Encode.TotalCodec Key (Link Name))
    {read : Link Name → Resolution Value} {rel : Naming.Relation (Link Name) Value}
    (sound : Sound read rel) {query : Key} {value : Value}
    (hit : (index layout).lookup key read query = some (.found value)) : value ∈ contents key rel layout := by
  obtain ⟨member, resolves⟩ := lookup_found layout key sound hit
  exact ⟨query, member, resolves⟩

theorem contents_ofContents (key : Encode.TotalCodec Key (Link Name))
    {rel : Naming.Relation (Link Name) Value} {chooseName : Value → Key} {values : Finset Value}
    (binding : Naming.Binding rel) (coherent : Coherent key rel chooseName values) :
    contents key rel (ofContents chooseName values) = (↑values : Set Value) :=
  Proofs.Formats.Dasl.NameLinkSet.contents_ofContents key binding coherent

/-- Canonical for this order and selector, not across naming policies. -/
theorem ofContents_eq_iff (key : Encode.TotalCodec Key (Link Name))
    {rel : Naming.Relation (Link Name) Value} {chooseName : Value → Key} {left right : Finset Value}
    (binding : Naming.Binding rel) (first : Coherent key rel chooseName left) (second : Coherent key rel chooseName right) :
    ofContents chooseName left = ofContents chooseName right ↔ left = right := by
  refine ⟨fun same => Finset.coe_injective ?_, congrArg (ofContents chooseName)⟩
  rw [← contents_ofContents key binding first, ← contents_ofContents key binding second, same]

theorem decodedBindings_binding (profile : Wire.Profile Name) (accept : Link Name → Bool)
    (objects : Encode.TotalCodec Object (Shallow Name)) {store : Naming.Relation Name ByteArray}
    (binding : Naming.Binding store) : Naming.Binding (decodedBindings profile accept objects store) :=
  Proofs.Formats.Dasl.NameLinkSet.decodedBindings_binding profile accept objects binding

/-- Sound in every store relation that contains the bytes observed by the reader. -/
theorem wireReader_sound (profile : Wire.Profile Name) (accept : Link Name → Bool)
    (objects : Encode.TotalCodec Object (Shallow Name)) {read : Name → Option ByteArray}
    {store : Naming.Relation Name ByteArray}
    (observed : ∀ ⦃name bytes⦄, read name = some bytes → store name bytes) :
    Sound (wireReader profile accept objects read) (decodedBindings profile accept objects store) :=
  Proofs.Formats.Dasl.NameLinkSet.wireReader_sound profile accept objects observed

end Silmaril.Formats.Dasl.NameLinkSet
