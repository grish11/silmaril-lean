module

public import Silmaril.Formats.Cbor.Events.Defs
public import Silmaril.Formats.Cbor.Value.Thms
import Silmaril.Proofs.Formats.Cbor.Events

/-!
# CBOR event streams: lemmas

* `itemEv_mem_wellFormed`: the bytes of an event stream are one well-formed CBOR item;
* `decodeEvents_encode`: decoding those bytes gives back the events, so `encodeEvents` is
  injective on event streams (`encodeEvents_injective`);
* `encodeEvents_toEvents`, `itemEv_toEvents`: the events of a definite-length value are an event
  stream whose bytes are `Value.encode`;
* examples: definite and indefinite containers, chunked strings, tags.
-/

@[expose] public section

namespace Silmaril.Formats.Cbor

theorem encodeEvents_append (a b : List Event) :
    encodeEvents (a ++ b) = encodeEvents a ++ encodeEvents b :=
  Silmaril.Proofs.Formats.Cbor.Events.encodeEvents_append a b

/-- The bytes of an event stream are one well-formed CBOR item. -/
theorem itemEv_mem_wellFormed {es : List Event} (h : ItemEv es) : encodeEvents es ∈ wellFormed :=
  Silmaril.Proofs.Formats.Cbor.Events.itemEv_item h

/-- Decoding the bytes of an event stream gives back the events. -/
theorem decodeEvents_encode {es : List Event} (h : ItemEv es) :
    decodeEvents (encodeEvents es) = some es :=
  Silmaril.Proofs.Formats.Cbor.Events.decodeEvents_encode h

theorem encodeEvents_injective {es fs : List Event} (h : ItemEv es) (h' : ItemEv fs)
    (he : encodeEvents es = encodeEvents fs) : es = fs :=
  Option.some.inj ((decodeEvents_encode h).symm.trans (he ▸ decodeEvents_encode h'))

theorem encodeEvents_toEvents (v : Value) : encodeEvents v.toEvents = v.encode :=
  Silmaril.Proofs.Formats.Cbor.Events.encodeEvents_toEvents v

theorem itemEv_toEvents (v : Value) (hv : v.Encodable) : ItemEv v.toEvents :=
  Silmaril.Proofs.Formats.Cbor.Events.itemEv_toEvents v hv

theorem toEvents_mem_language (v : Value) (hv : v.Encodable) : v.toEvents ∈ Events.language :=
  itemEv_toEvents v hv

/-! ## Examples -/

section Examples

-- `[_ 1, [2, 3], [_ 4, 5]]` (RFC 8949 Appendix A): definite and indefinite arrays, both
-- bracketed by begin and end events.
example : decodeEvents [0x9F, 0x01, 0x82, 0x02, 0x03, 0x9F, 0x04, 0x05, 0xFF, 0xFF] =
    some [.beginArray none, .uint 1, .beginArray (some 2), .uint 2, .uint 3,
      .endArray (some 2), .beginArray none, .uint 4, .uint 5, .endArray none,
      .endArray none] := by decide
-- `(_ h'0102', h'030405')`: an indefinite byte string as its chunks.
example : decodeEvents [0x5F, 0x42, 0x01, 0x02, 0x43, 0x03, 0x04, 0x05, 0xFF] =
    some [.beginIndefBytes, .bytes [1, 2], .bytes [3, 4, 5], .endIndefString] := by decide
-- A bignum `2(h'01')` is a tag event followed by its content.
example : decodeEvents [0xC2, 0x41, 0x01] = some [.tag 2, .bytes [1]] := by decide
-- `{_ 0: 0 }` with a break in the value position does not decode.
example : decodeEvents [0xBF, 0x00, 0xFF] = none := by decide
-- A non-shortest head gives the same events as the shortest one, so events fix bytes only up to
-- argument width.
example : decodeEvents [0x18, 0x00] = decodeEvents [0x00] := by decide
-- The events of a value re-encode to its bytes.
example : encodeEvents (Value.map [(.text [0x61], .uint 1)]).toEvents = [0xA1, 0x61, 0x61, 0x01] := by
  decide

end Examples

end Silmaril.Formats.Cbor

end
