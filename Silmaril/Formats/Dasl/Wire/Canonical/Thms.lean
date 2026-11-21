module

public import Silmaril.Formats.Dasl.Wire.Canonical.Defs
public import Silmaril.Formats.Dasl.Encode.Defs
import Silmaril.Proofs.Formats.Dasl.WireCanonical

public section

namespace Silmaril.Formats.Dasl.Wire

open Silmaril.Formats.Cbor

theorem canonical_projection {Name : Type} (value : Shallow Name) : lower (canonicalOrder (toOrdered value)) = value :=
  Proofs.Formats.Dasl.WireCanonical.projection value

theorem parse_render {value : Shallow Cid} {bytes : ByteArray} (encodable : (canonicalModel value).Encodable)
    (rendered : render? value = some bytes) : parse? bytes = some value :=
  Proofs.Formats.Dasl.WireCanonical.parse_render encodable rendered

/-- An encodable canonical model with the correct typed CID tags renders
to the exact canonical bytes, and parsing those bytes recovers the abstract AST. -/
theorem canonical_roundtrip (value : Shallow Cid)
    (valid : ∀ link ∈ Drisl.links (toOrdered value), ValidLink link)
    (encodable : (canonicalModel value).Encodable)
    (ordered : Drisl.canonicalMaps (canonicalModel value) = true) :
    let bytes := (canonicalModel value).encode.toByteArray
    render? value = some bytes ∧ parse? bytes = some value :=
  Proofs.Formats.Dasl.WireCanonical.roundtrip value valid encodable ordered

theorem parse_renderBounded {value : Shallow Cid} {bytes : ByteArray}
    (rendered : renderBounded? value = some bytes) : parse? bytes = some value := by
  unfold renderBounded? at rendered
  split at rendered
  · exact parse_render ‹_› rendered
  · contradiction

theorem renderBounded_serializes {value : Shallow Cid} {bytes : ByteArray}
    (rendered : renderBounded? value = some bytes) : Serializes value bytes := by
  have recover := parse_renderBounded rendered
  unfold renderBounded? at rendered
  split at rendered
  · exact ⟨rendered, recover⟩
  · contradiction

/-- Every input accepted by the typed canonical parser reprints byte for byte,
including recursively sorted dictionaries reconstructed from finite key sets. -/
theorem render_of_parse {bytes : ByteArray} {value : Shallow Cid} (parsed : parse? bytes = some value) :
    render? value = some bytes := (Proofs.Formats.Dasl.WireCanonical.reprint parsed).1

theorem renderBounded_of_parse {bytes : ByteArray} {value : Shallow Cid} (parsed : parse? bytes = some value) :
    renderBounded? value = some bytes := by
  obtain ⟨rendered, encodable⟩ := Proofs.Formats.Dasl.WireCanonical.reprint parsed
  simpa [renderBounded?, encodable] using rendered

theorem parse_iff_renderBounded {bytes : ByteArray} {value : Shallow Cid} :
    parse? bytes = some value ↔ renderBounded? value = some bytes :=
  ⟨renderBounded_of_parse, parse_renderBounded⟩

@[expose] def canonicalCodec : Encode.PartialCodec (Shallow Cid) ByteArray :=
  ⟨renderBounded?, parse?, fun _ _ => parse_renderBounded⟩

end Silmaril.Formats.Dasl.Wire
