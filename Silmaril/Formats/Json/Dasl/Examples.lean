module
import Silmaril.Formats.Json.Dasl.Thms

namespace Silmaril.Formats.JsonDasl

private def utf8 (input : String) : Bytes := ⟨input.toUTF8⟩

example : (parseSafeAbstract? (utf8 "9007199254740991")).isSome = true := by decide +kernel
example : (parseSafeAbstract? (utf8 "9007199254740992")).isNone = true := by decide +kernel
example : (parseI64Abstract? (utf8 "-9223372036854775808")).isSome = true := by decide +kernel
example : (parseI64Abstract? (utf8 "9223372036854775808")).isNone = true := by decide +kernel
example : (parseI64Abstract? (utf8 "0.1")).isNone = true := by
  have parsed : JsonWire.parse? (utf8 "0.1") = some (.scalar (some (.number ⟨false, 1, -1⟩))) := rfl
  have fractional : JsonWire.Decimal.toInt? ⟨false, 1, -1⟩ = none := by simp [JsonWire.Decimal.toInt?]
  simp [parseI64Abstract?, Dasl.Encode.TotalCodec.parseAbstract?, parseI64?, JsonWire.parseInteger?,
    parsed, JsonWire.mapNumbers?, fractional]

private def duplicateSurrogates : RfcJsonBytes :=
  .map (.objCons [0xD800] (.scalar (.inl (some (.number ⟨true, 0, -2⟩))))
    (.objCons [0xD800] (.scalar (.inr ⟨#[0xFF, 0x00]⟩)) .objNil))

example : rfcBytes.fromAbstract? (rfcBytes.intoAbstract duplicateSurrogates) = some duplicateSurrogates :=
  rfcBytes.from_intoAbstract duplicateSurrogates

example : (parseRfcAbstract? (utf8 "{\"\\uD800\":-0.00,\"\\uD800\":1e999}")).isSome = true := by
  decide +kernel

end Silmaril.Formats.JsonDasl
