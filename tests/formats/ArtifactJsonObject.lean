module

import Silmaril.Formats.Dasl.JsonObject.Thms
meta import Silmaril.Formats.Dasl.JsonObject.Defs

open Silmaril.Formats Silmaril.Formats.Cbor Silmaril.Formats.Dasl

private def emptyObject : JsonObject.Object := ⟨.objNil, by
  refine ⟨by simp [JsonObject.ordered, JsonObject.strictKeys], ?_⟩
  have size : (JsonObject.body .objNil).length = 5 := by with_unfolding_all rfl
  rw [size]
  decide +kernel⟩

example : JsonObject.decode? (JsonObject.encode emptyObject) = some emptyObject :=
  JsonObject.decode_encode emptyObject

example : JsonObject.encode emptyObject = [0x45, 0x53, 0x4a, 0x01, 0x7b, 0x7d] := by
  with_unfolding_all rfl

private def localName (name : String) (_ : List UInt8) : Prop := name = "local"

example : ∃! name, JsonObject.names localName name emptyObject := by
  apply JsonObject.exactly_one_name (observe := localName) _ (fun _ => ⟨"local", rfl⟩)
  intro bytes firstName secondName first second
  exact first.trans second.symm

private def utf8 (text : String) : Bytes := ⟨text.toUTF8⟩

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def objectBytes (text : String) : IO (List UInt8) := do
  let some object := JsonObject.parse? (utf8 text) | throw (IO.userError s!"profile rejected {text}")
  pure (JsonObject.encode object)

private def envelope (text : String) : List UInt8 :=
  (Value.bytes ([0x53, 0x4a, 0x01] ++ (utf8 text).toList)).encode

#print axioms JsonObject.decode_encode
#print axioms JsonObject.exactly_one_name
#print axioms JsonObject.names_binding

public def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected an output path for the JSON object fixture")
  let canonical := r#"{"z":[1,2],"\u0061":{"$bytes":"\uDEAD","b":-0e-8,"x":9007199254740993.1}}"#
  let permuted := r#"{ "a": {"x":9007199254740993.1,"b":-0e-8,"$bytes":"\uDEAD"}, "z":[1,2] }"#
  let bytes ← objectBytes canonical
  check (bytes == (← objectBytes permuted)) "member order or key escaping changed canonical bytes"
  let some back := JsonObject.decode? bytes | throw (IO.userError "envelope did not decode")
  check (JsonObject.encode back == bytes) "re-encoding changed the exact object"
  check (bytes == envelope (JsonWire.render JsonWire.Decimal.literal (.map back.val)))
    "versioned body did not contain the exact canonical JSON representative"
  let duplicate := utf8 r#"{"outer":{"x":1,"\u0078":2}}"#
  check (JsonWire.parse? duplicate).isSome "RFC syntax must still accept duplicate members"
  check (JsonObject.parse? duplicate).isNone "profile must reject duplicate members"
  check (JsonObject.parse? (utf8 "[{}]")).isNone "profile requires a top-level object"
  check ((← objectBytes "{\"a\":1}") == (← objectBytes "{\"a\":1e+0}"))
    "equivalent decimal triples had different bytes"
  check ((← objectBytes "{\"a\":1}") != (← objectBytes "{\"a\":1.0}")) "decimal fields were collapsed"
  check ((← objectBytes "{\"a\":-0}") != (← objectBytes "{\"a\":0}")) "negative zero was collapsed"
  check ((← objectBytes r#"{"a":"\uDEAD"}"#) != (← objectBytes r#"{"a":"\uDEAE"}"#))
    "non-scalar code units were collapsed"
  check ((← objectBytes "{\"a\":[2,1]}") != (← objectBytes "{\"a\":[1,2]}")) "array order was lost"
  check (JsonObject.decode? (envelope "{ }")).isNone "noncanonical JSON spelling accepted in envelope"
  check (JsonObject.decode? (envelope permuted)).isNone "noncanonical byte representative accepted"
  check (JsonObject.decode? [0x45, 0x53, 0x4a, 2, 0x7b, 0x7d]).isNone "unknown version was accepted"
  IO.FS.writeBinFile path bytes.toByteArray
