module

public import Silmaril.Formats.Dasl.RawStore.Defs
public import Silmaril.Formats.Dasl.Resolve.Thms
public import Silmaril.Formats.Dasl.Wire.Thms
import Silmaril.Proofs.Formats.Dasl.RawStore

public section

namespace Silmaril.Formats.Dasl.RawStore

open Silmaril.Semantics.Naming

/-- The concrete canonical-CBOR object view; raw CID payloads are not parsed. -/
def daslDecoder : Decoder Wire.Cid :=
  ⟨Wire.IsObjectCid, Wire.IsRawCid, fun _ => Wire.object_raw_disjoint, Wire.parse?⟩

theorem readObject_found_iff {read : Wire.Cid → Option ByteArray} {name : Wire.Cid} {value : Shallow Wire.Cid} :
    Wire.readObject read name = .found value ↔ (daslDecoder.view (graph read)).objects name value :=
  Proofs.Formats.Dasl.RawStore.readObject_found_iff

/-- Absence is relative to this byte reader, and only in the object codec domain. -/
theorem readObject_missing_iff {read : Wire.Cid → Option ByteArray} {name : Wire.Cid} :
    Wire.readObject read name = .missing ↔ Wire.IsObjectCid name ∧ read name = none :=
  Proofs.Formats.Dasl.RawStore.readObject_missing_iff

theorem readObject_invalidWire_iff {read : Wire.Cid → Option ByteArray} {name : Wire.Cid} :
    Wire.readObject read name = .invalidWire ↔ ¬ Wire.IsObjectCid name ∨
      ∃ bytes, read name = some bytes ∧ Wire.parse? bytes = none :=
  Proofs.Formats.Dasl.RawStore.readObject_invalidWire_iff

variable {Name : Type} {decoder : Decoder Name} {base defaults extended policy : Blocks Name}

theorem Decoder.view_binding (bound : Binding base) : (decoder.view base).Binding :=
  Proofs.Formats.Dasl.RawStore.view_binding bound

theorem Decoder.view_disjoint : (decoder.view base).DisjointDomains :=
  fun _ _ _ object raw => decoder.disjoint object.1 raw.1

theorem Decoder.view_mono (incl : Subset base extended) : (decoder.view base).Subset (decoder.view extended) :=
  ⟨fun _ _ ⟨codec, bytes, hit, parsed⟩ => ⟨codec, bytes, incl hit, parsed⟩,
   fun _ _ ⟨codec, hit⟩ => ⟨codec, incl hit⟩⟩

/-- Successful reads are included in every raw extension of the reader's graph;
this does not certify the extension's binding or the bytes' hash integrity. -/
theorem readObject_sound {read : Wire.Cid → Option ByteArray} {bytes : Blocks Wire.Cid}
    (included : Subset (graph read) bytes) {name : Wire.Cid} {value : Shallow Wire.Cid}
    (found : Wire.readObject read name = .found value) : (daslDecoder.view bytes).objects name value :=
  (Decoder.view_mono included).1 (readObject_found_iff.mp found)

theorem completion_iff {root : Name} : Completes decoder policy base extended root ↔
    Subset base extended ∧ Binding extended ∧ Subset extended policy ∧
      (∃ source, (decoder.view extended).objects root source) ∧
      Acc (Depends (decoder.view extended)) root ∧ ClosedBelow (decoder.view extended) root :=
  Proofs.Formats.Dasl.RawStore.completion_iff

theorem fill_completes {root : Name} (baseBound : Binding base) (defaultBound : Binding defaults)
    (baseAllowed : Subset base policy)
    (defaultAllowed : ∀ ⦃name bytes⦄, (¬ ∃ old, base name old) → defaults name bytes → policy name bytes)
    (found : ∃ source, (decoder.view (fill base defaults)).objects root source)
    (access : Acc (Depends (decoder.view (fill base defaults))) root)
    (closed : ClosedBelow (decoder.view (fill base defaults)) root) : Completes decoder policy base (fill base defaults) root :=
  Proofs.Formats.Dasl.RawStore.fill_completes baseBound defaultBound baseAllowed defaultAllowed found access closed

theorem no_completion_of_malformed_root {root : Name} {bytes : ByteArray}
    (present : base root bytes) (malformed : decoder.parse? bytes = none) :
    ¬ Completes decoder policy base extended root :=
  Proofs.Formats.Dasl.RawStore.no_completion_of_malformed_root present malformed

theorem no_completion_of_self_link {root : Name} {bytes : ByteArray} {source : Shallow Name}
    (present : base root bytes) (codec : decoder.objectName root)
    (parsed : decoder.parse? bytes = some source) (linked : Link.obj root ∈ source.directLinks) :
    ¬ Completes decoder policy base extended root :=
  Proofs.Formats.Dasl.RawStore.no_completion_of_self_link present codec parsed linked

theorem no_completion_of_rejected_present {name : Name} {bytes : ByteArray}
    (present : base name bytes) (rejected : ¬ policy name bytes) {root : Name} :
    ¬ Completes decoder policy base extended root :=
  fun completed => rejected (completed.2.2.1 (completed.1 present))

end Silmaril.Formats.Dasl.RawStore
