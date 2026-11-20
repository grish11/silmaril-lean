module

import Silmaril.Formats.Cbor.Drisl.Debug.Text.Thms
import Silmaril.Formats.Cbor.Drisl.Model.Thms
meta import Silmaril.Formats.Cbor.Drisl.Debug.Text.Defs
meta import Silmaril.Formats.Cbor.Drisl.Model.Defs

open Silmaril.Formats Silmaril.Formats.Cbor Silmaril.Formats.Cbor.Drisl
open Silmaril.Formats.Cbor.Drisl.Debug

private def text (value : String) : Bytes := ⟨value.toUTF8⟩

private def check (success : Bool) (label : String) : IO Unit :=
  unless success do throw (IO.userError label)

private def floatRoundtrip (bits : Nat) : IO Unit := do
  if valid : okFloat64 bits = true then
    let value : Ordered := .scalar (.data (.number (.float ⟨bits, valid⟩)))
    let wire := renderText (drislCodec .any) .prefix value
    match parseText? (drislCodec .any) .prefix wire with
    | some (.scalar (.data (.number (.float restored)))) => check (restored.val == bits) "exact float bits"
    | _ => throw (IO.userError "failed float text roundtrip")
  else throw (IO.userError "invalid fixture bits")

public def main : IO Unit := do
  for policy in [Escape.prefix, .suffix] do
    let value : JsonWithBytes.Ordered := .map (.objCons "" (.scalar .null)
      (.objCons "$" (.scalar (.bytes [0, 0xFB, 0xFF]))
      (.objCons "$$$" (.list (.cons (.map (.objCons "$bytes" (.scalar (.string "AA")) .objNil)) .nil))
      (.objCons "雪🌲" (.scalar (.string "é\n")) .objNil))))
    let wire := renderJsonWithBytes policy value
    check ((parseJsonWithBytes? policy wire).map (renderJsonWithBytes policy) == some wire) "nested escaping"
    check ((parseJsonWithBytes? policy (text "{\"$bytes\":0}")).isNone) "malformed wrapper must not fall back"
    check ((parseJsonWithBytes? policy (text "{\"$bytes\":\"AB\"}")).isNone) "nonzero base64 tail bits"
    check ((parseJsonWithBytes? policy (text "{\"$bytes\":\"AA==\"}")).isNone) "canonical unpadded base64"
    check ((parseJsonWithBytes? policy (text "{\"abc\":0,\"abc\":1}")).isNone) "duplicate fields"
    check ((parseJsonWithBytes? policy (text "{\"abc\":0,\"\\u0061bc\":1}")).isNone) "duplicate escaped spelling"
    check ((parseJsonWithBytes? policy (text "\"\\ud800\"")).isNone) "unpaired surrogate"
    check ((parseJsonWithBytes? policy (text "{\"$odd\":0}")).isNone) "noncanonical ordinary key"
    check ((parseJsonWithBytes? policy (text "{\"$links\":\"abc\"}")).isNone) "plural key is not a wrapper"
  check ((parseJsonWithBytes? .none (text "{\"$links\":\"abc\"}")).isSome) "plural is ordinary unescaped"
  check ((parseJsonWithBytes? .none (text "{\"$bytes\":null,\"\":0}")).isSome) "reserved key only wraps singleton"
  let literal : JsonWithBytes.Ordered := .map (.objCons "$bytes" (.scalar (.string "")) .objNil)
  let emptyBytes : JsonWithBytes.Ordered := .scalar (.bytes [])
  check (renderJsonWithBytes .none literal == renderJsonWithBytes .none emptyBytes) "unescaped singleton collision"
  for policy in [Escape.prefix, .suffix] do
    check (renderJsonWithBytes policy literal != renderJsonWithBytes policy emptyBytes) "escaping separates literal and bytes"
  let linkText := text "{\"$link\":\"bafkreifn5yxi7nkftsn46b6x26grda57ict7md2xuvfbsgkiahe2e7vnq4\"}"
  check ((parseText? (atprotoCodec .dasl) .none linkText).isSome) "DRISL example CID"
  check ((parseI64Text? .dasl .none linkText).isNone) "i64 text restriction rejects links"
  check ((parseJsonWithBytes? .none linkText).isNone) "JSON with bytes is link-free"
  let blake := [1, 0x71, 0x1E, 32] ++ List.replicate 32 (0 : UInt8)
  check (CidProfile.bdasl.accepts blake && CidProfile.any.accepts blake && !CidProfile.dasl.accepts blake) "CID restrictions"
  check (CidProfile.any.accepts [1, 0x81, 1, 0, 1, 0]) "multi-byte codec"
  check (!CidProfile.any.accepts [1, 0x81, 0, 0, 1, 0]) "overlong varint"
  check (!CidProfile.any.accepts (blake ++ [0])) "trailing CID bytes"
  check ((decimalI64? ⟨false, 9223372036854775807, 0⟩).isSome) "i64 max"
  check ((decimalI64? ⟨true, 9223372036854775808, 0⟩).isSome) "i64 min"
  check ((decimalI64? ⟨false, 9223372036854775808, 0⟩).isNone) "positive i64 overflow"
  check ((decimalI64? ⟨true, 9223372036854775809, 0⟩).isNone) "negative i64 overflow"
  check ((decimalI64? ⟨false, 100, -2⟩).isSome) "other exact integer spellings"
  check ((Number.ofDecimal? ⟨false, 18446744073709551616, 0⟩).isNone) "unsigned overflow"
  check ((Number.ofDecimal? ⟨true, 18446744073709551616, 0⟩).isSome) "DRISL lower integer limit"
  check ((Number.ofDecimal? ⟨true, 0, -1⟩).isNone) "negative zero must not collapse"
  check ((Number.ofDecimal? ⟨false, 1, -1⟩).isNone) "decimal 0.1 would require rounding"
  match Number.ofDecimal? ⟨false, 5, -1⟩ with
  | some (.float bits) => check (bits.val == 0x3FE0000000000000) "exact decimal 0.5"
  | _ => throw (IO.userError "exact decimal 0.5 failed")
  check ((parseText? (drislCodec .any) .prefix (text "0.5")).isSome) "ordinary exact fractional spelling"
  check ((parseI64Text? .any .prefix (text "0.5")).isNone) "ATProto debug rejects fractional numbers"
  let integerOne : Ordered := .scalar (.data (.number (.integer (.uint 1))))
  let doubleOne : Ordered := .scalar (.data (.number (.float ⟨0x3FF0000000000000, by decide⟩)))
  check (renderText (drislCodec .any) .prefix integerOne != renderText (drislCodec .any) .prefix doubleOne)
    "exact double spelling must not collide with the equal integer"
  for bits in [0, 1, 0x000FFFFFFFFFFFFF, 0x0010000000000000, 0x3FF0000000000000,
      0x3FF0000000000001, 0x7FEFFFFFFFFFFFFF, 0xBFE0000000000000, 0x8000000000000001] do
    floatRoundtrip bits
  for bits in [0x8000000000000000, 0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000001] do
    check ((drislCbor.readNumber? (.float 8 bits)).isNone) "negative zero, infinity, or NaN"
  check ((i64Cbor.readNumber? (.float 8 0)).isNone) "ATProto rejects floats"
  let unsorted : Value := .map [(.text [0x61, 0x61], .uint 1), (.text [0x7A], .uint 2)]
  check ((interpretCbor? i64Cbor emptyCid unsorted).isSome) "unordered CBOR value model"
  check ((parseCbor? i64Cbor emptyCid unsorted.encode).isNone) "canonical bytes require CBOR map order"
  let canonical : Value := .map [(.text [0x7A], .uint 2), (.text [0x61, 0x61], .uint 1)]
  let ordered := interpretCbor? i64Cbor emptyCid unsorted
  check ((ordered.bind (renderCbor? i64Cbor emptyCid)) == some canonical.encode) "canonical rendering"
  check ((parseCbor? i64Cbor emptyCid [0x18, 0]).isNone) "overlong CBOR head"
  check ((parseCbor? i64Cbor emptyCid [0, 0]).isNone) "trailing CBOR item"
  let taggedCid : Value := .tag 42 (.bytes (0 :: blake))
  check ((parseCbor? i64Cbor (Cid.codec .bdasl) taggedCid.encode).isSome) "CBOR ATProto extension accepts BDASL"
  check ((parseI64Cbor? .bdasl taggedCid.encode).isNone) "i64 CBOR restriction rejects links"
