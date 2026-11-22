module

public import Silmaril.Formats.Dasl.JsonObject.Defs
import Silmaril.Formats.Cbor.Value.Thms
import Silmaril.Formats.JsonWire.Encoding.Thms

public section

namespace Silmaril.Proofs.Formats.Dasl.JsonObject

open Silmaril.Formats Silmaril.Formats.Cbor Silmaril.Formats.Dasl.JsonObject

theorem decode_encode (object : Object) : decode? (encode object) = some object := by
  have wire : Cbor.decode (encode object) = some (.bytes (body object.val)) :=
    Cbor.decode_encode _ object.property.2
  have text := JsonWire.parse_encode (.map object.val)
  unfold decode?
  rw [wire]
  change (do
    let .map fields ← JsonWire.parse? (Bytes.ofList (JsonWire.encode (.map object.val)).toList) | none
    let parsed ← admit? fields
    if encode parsed = encode object then some parsed else none) = some object
  rw [Bytes.ofList_toList, text]
  have admitted : admit? object.val = some object := dite_eq_left object.property
  simp [admitted]

end Silmaril.Proofs.Formats.Dasl.JsonObject
