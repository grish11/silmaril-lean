module

public import Silmaril.Formats.Cbor.Drisl.Debug.Text.Defs
public import Silmaril.Formats.Cbor.Drisl.Debug.Thms
public import Silmaril.Formats.Cbor.Drisl.Convert.Thms
public import Silmaril.Formats.Cbor.Drisl.Cid.Thms
public import Silmaril.Formats.Cbor.Drisl.Number.Thms
public import Silmaril.Formats.JsonWire.Thms
public import Silmaril.Formats.JsonWire.Encoding.Thms
import Silmaril.Proofs.Formats.Cbor.Drisl.DebugText

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl.Debug

theorem ofWire_toWire (tree : Tree) : ofWire? (toWire tree) = some tree :=
  Proofs.Formats.Cbor.Drisl.DebugText.ofWire_toWire tree

theorem drisl_decode_encode (profile : CidProfile) (policy : Escape) (value : Ordered (Cid profile))
    (safe : CollisionFree policy value) : decode? (drislCodec profile) policy
      (encode (drislCodec profile) policy value) = some value :=
  decode_encode _ Number.readDecimal_toDecimal (Cid.read_render profile) policy value safe

theorem atproto_decode_encode (profile : CidProfile) (policy : Escape) (value : OrderedATProto (Cid profile))
    (safe : CollisionFree policy value) : decode? (atprotoCodec profile) policy
      (encode (atprotoCodec profile) policy value) = some value :=
  decode_encode _ decimalI64_intDecimal (Cid.read_render profile) policy value safe

theorem drisl_decode_encode_escaped (profile : CidProfile) (policy : Escape) (escaped : policy ≠ .none)
    (value : Ordered (Cid profile)) : decode? (drislCodec profile) policy
      (encode (drislCodec profile) policy value) = some value :=
  drisl_decode_encode profile policy value (escaped_safe policy escaped value)

theorem atproto_decode_encode_escaped (profile : CidProfile) (policy : Escape) (escaped : policy ≠ .none)
    (value : OrderedATProto (Cid profile)) : decode? (atprotoCodec profile) policy
      (encode (atprotoCodec profile) policy value) = some value :=
  atproto_decode_encode profile policy value (escaped_safe policy escaped value)

theorem drisl_encode_injective (profile : CidProfile) (policy : Escape) (escaped : policy ≠ .none) :
    Function.Injective (encode (drislCodec profile) policy (index := .val)) :=
  fun left right same => encode_injective _ Number.readDecimal_toDecimal (Cid.read_render profile)
    policy (escaped_safe policy escaped left) (escaped_safe policy escaped right) same

theorem atproto_encode_injective (profile : CidProfile) (policy : Escape) (escaped : policy ≠ .none) :
    Function.Injective (encode (atprotoCodec profile) policy (index := .val)) :=
  fun left right same => encode_injective _ decimalI64_intDecimal (Cid.read_render profile)
    policy (escaped_safe policy escaped left) (escaped_safe policy escaped right) same

theorem atproto_agrees_with_i64 (profile : CidProfile) (policy : Escape) (value : JsonWithBytes.OrderedI64) :
    encode (atprotoCodec profile) policy (embedI64 value) =
      encode jsonWithBytesI64Codec policy (embedI64 value) :=
  Proofs.Formats.Cbor.Drisl.DebugText.atproto_agrees profile policy value

theorem drisl_agrees_with_atproto (profile : CidProfile) (policy : Escape) (value : OrderedATProto (Cid profile)) :
    encode (drislCodec profile) policy (widenATProto value) = encode (atprotoCodec profile) policy value :=
  Proofs.Formats.Cbor.Drisl.DebugText.drisl_agrees profile policy value

theorem renderText_atproto_agrees_with_i64 (profile : CidProfile) (policy : Escape)
    (value : JsonWithBytes.OrderedI64) :
    renderText (atprotoCodec profile) policy (embedI64 value) =
      renderText jsonWithBytesI64Codec policy (embedI64 value) :=
  congrArg (JsonWire.encode ∘ toWire) (atproto_agrees_with_i64 profile policy value)

theorem renderText_drisl_agrees_with_atproto (profile : CidProfile) (policy : Escape)
    (value : OrderedATProto (Cid profile)) :
    renderText (drislCodec profile) policy (widenATProto value) = renderText (atprotoCodec profile) policy value :=
  congrArg (JsonWire.encode ∘ toWire) (drisl_agrees_with_atproto profile policy value)

theorem renderText_policies_agree {Input Link : Type} (codec : Codec Input JsonWire.Decimal Link)
    (left right : Escape) (value : RawJson (Scalar Input Link)) (valid : KeysSatisfy NoDollar value) :
    renderText codec left value = renderText codec right value :=
  congrArg (JsonWire.encode ∘ toWire) (policies_agree codec left right value valid)

theorem i64_roundtrip_unordered (profile : CidProfile) (value : JsonWithBytes.OrderedI64)
    (valid : value.WellFormed) (safe : KeysSatisfy NoReserved value) :
    ∃ restored : JsonWithBytes.OrderedI64,
      (decode? (atprotoCodec profile) .none (encode (atprotoCodec profile) .none (embedI64 value))).bind
          removeLinks? = some restored ∧
      ∃ restoredValid : restored.WellFormed, restored.toJson restoredValid = value.toJson valid := by
  have safe' : KeysSatisfy NoReserved (embedI64 (Cid := Cid profile) value) :=
    (keysSatisfy_mapScalar NoReserved Scalar.data value).mpr safe
  exact ⟨value, by rw [atproto_decode_encode _ _ _ (reserved_safe _ safe')]; exact removeLinks_embedI64 _, valid, rfl⟩

theorem i64_roundtrip_unordered_noDollar (profile : CidProfile) (value : JsonWithBytes.OrderedI64)
    (valid : value.WellFormed) (safe : KeysSatisfy NoDollar value) :
    ∃ restored : JsonWithBytes.OrderedI64,
      (decode? (atprotoCodec profile) .none (encode (atprotoCodec profile) .none (embedI64 value))).bind
          removeLinks? = some restored ∧
      ∃ restoredValid : restored.WellFormed, restored.toJson restoredValid = value.toJson valid :=
  i64_roundtrip_unordered profile value valid (noDollar_noReserved _ safe)

theorem textLanguage_le_json {Input Link : Type} (codec : Codec Input JsonWire.Decimal Link)
    (policy : Escape) : textLanguage codec policy ≤ JsonBytes.language .rfc8259 :=
  Proofs.Formats.Cbor.Drisl.DebugText.textLanguage_le_json codec policy

theorem parseText_eq_some_iff {Input Link : Type} (codec : Codec Input JsonWire.Decimal Link)
    (policy : Escape) {bytes : Bytes} {value : RawJson (Scalar Input Link)} :
    parseText? codec policy bytes = some value ↔ value.WellFormed ∧
      ∃ source tree, JsonWire.parse? bytes = some source ∧ ofWire? source = some tree ∧
        decode? codec policy tree = some value :=
  Proofs.Formats.Cbor.Drisl.DebugText.parse_eq_some_iff codec policy

/-- On duplicate-free trees, escaping removes the need for a collision guard;
for no escape, the guard excludes only ordinary reserved singletons. -/
theorem parseText_renderText {Input Link : Type} (codec : Codec Input JsonWire.Decimal Link)
    (numberInv : ∀ value, codec.readNumber? (codec.number value) = some value)
    (linkInv : ∀ value, codec.readLink? (codec.link value) = some value)
    (policy : Escape) (value : RawJson (Scalar Input Link))
    (valid : value.WellFormed) (safe : CollisionFree policy value) :
    parseText? codec policy (renderText codec policy value) = some value :=
  (parseText_eq_some_iff codec policy).mpr ⟨valid, _, _, JsonWire.parse_encode _,
    ofWire_toWire _, decode_encode codec numberInv linkInv policy value safe⟩

theorem renderText_injectiveOn {Input Link : Type} (codec : Codec Input JsonWire.Decimal Link)
    (numberInv : ∀ value, codec.readNumber? (codec.number value) = some value)
    (linkInv : ∀ value, codec.readLink? (codec.link value) = some value) (policy : Escape) :
    Set.InjOn (renderText codec policy)
      { value : RawJson (Scalar Input Link) | value.WellFormed ∧ CollisionFree policy value } := by
  intro left ⟨leftValid, leftSafe⟩ right ⟨rightValid, rightSafe⟩ same
  rw [← Option.some.injEq, ← parseText_renderText codec numberInv linkInv policy left leftValid leftSafe,
    ← parseText_renderText codec numberInv linkInv policy right rightValid rightSafe, same]

theorem renderText_parseText_on_image {Input Link : Type} (codec : Codec Input JsonWire.Decimal Link)
    (numberInv : ∀ value, codec.readNumber? (codec.number value) = some value)
    (linkInv : ∀ value, codec.readLink? (codec.link value) = some value)
    (policy : Escape) (value : RawJson (Scalar Input Link))
    (valid : value.WellFormed) (safe : CollisionFree policy value) :
    (parseText? codec policy (renderText codec policy value)).map (renderText codec policy) =
      some (renderText codec policy value) := by
  rw [parseText_renderText codec numberInv linkInv policy value valid safe, Option.map_some]

theorem drisl_parse_renderText (profile : CidProfile) (policy : Escape) (value : Ordered (Cid profile))
    (valid : value.WellFormed) (safe : CollisionFree policy value) :
    parseText? (drislCodec profile) policy (renderText (drislCodec profile) policy value) = some value :=
  parseText_renderText _ Number.readDecimal_toDecimal (Cid.read_render profile) policy value valid safe

theorem atproto_parse_renderText (profile : CidProfile) (policy : Escape) (value : OrderedATProto (Cid profile))
    (valid : value.WellFormed) (safe : CollisionFree policy value) :
    parseText? (atprotoCodec profile) policy (renderText (atprotoCodec profile) policy value) = some value :=
  parseText_renderText _ decimalI64_intDecimal (Cid.read_render profile) policy value valid safe

theorem drisl_parse_renderText_escaped (profile : CidProfile) (policy : Escape) (escaped : policy ≠ .none)
    (value : Ordered (Cid profile)) (valid : value.WellFormed) :
    parseText? (drislCodec profile) policy (renderText (drislCodec profile) policy value) = some value :=
  drisl_parse_renderText profile policy value valid (escaped_safe policy escaped value)

theorem atproto_parse_renderText_escaped (profile : CidProfile) (policy : Escape) (escaped : policy ≠ .none)
    (value : OrderedATProto (Cid profile)) (valid : value.WellFormed) :
    parseText? (atprotoCodec profile) policy (renderText (atprotoCodec profile) policy value) = some value :=
  atproto_parse_renderText profile policy value valid (escaped_safe policy escaped value)

theorem parse_renderJsonWithBytes (policy : Escape) (value : JsonWithBytes.Ordered)
    (valid : value.WellFormed) (safe : CollisionFree policy (value.mapScalar (Scalar.data (Cid := Empty)))) :
    parseJsonWithBytes? policy (renderJsonWithBytes policy value) = some value := by
  have roundtrip := parseText_renderText jsonWithBytesCodec (fun _ => rfl) (fun link => nomatch link)
    policy (value.mapScalar Scalar.data)
    ((Proofs.Formats.Cbor.Drisl.DebugText.wellFormed_mapScalar _ value).mpr valid) safe
  rw [parseJsonWithBytes?, renderJsonWithBytes, roundtrip]
  exact removeLinks_mapScalar_data value

theorem parse_renderJsonWithBytes_escaped (policy : Escape) (escaped : policy ≠ .none)
    (value : JsonWithBytes.Ordered) (valid : value.WellFormed) :
    parseJsonWithBytes? policy (renderJsonWithBytes policy value) = some value :=
  parse_renderJsonWithBytes policy value valid (escaped_safe policy escaped _)

theorem parseI64Text_iff (profile : CidProfile) (policy : Escape) (bytes : Bytes) (value : JsonWithBytes.OrderedI64) :
    parseI64Text? profile policy bytes = some value ↔ AtprotoTextRep profile policy bytes (embedI64 value) :=
  restrictToI64_iff _ value

theorem parseI64Text_renderText (profile : CidProfile) (policy : Escape) (value : JsonWithBytes.OrderedI64)
    (valid : value.WellFormed) (safe : CollisionFree policy (embedI64 (Cid := Cid profile) value)) :
    parseI64Text? profile policy (renderText (atprotoCodec profile) policy (embedI64 value)) = some value :=
  (parseI64Text_iff profile policy _ value).mpr (atproto_parse_renderText profile policy (embedI64 value)
    ((Proofs.Formats.Cbor.Drisl.DebugText.wellFormed_mapScalar _ value).mpr valid) safe)

theorem i64_text_roundtrip_unordered (profile : CidProfile) (value : JsonWithBytes.OrderedI64)
    (valid : value.WellFormed) (safe : KeysSatisfy NoReserved value) :
    ∃ restored : JsonWithBytes.OrderedI64,
      parseI64Text? profile .none (renderText (atprotoCodec profile) .none (embedI64 value)) = some restored ∧
      ∃ restoredValid : restored.WellFormed, restored.toJson restoredValid = value.toJson valid :=
  ⟨value, parseI64Text_renderText profile .none value valid
    (reserved_safe _ ((keysSatisfy_mapScalar NoReserved Scalar.data value).mpr safe)), valid, rfl⟩

theorem i64_text_roundtrip_unordered_noDollar (profile : CidProfile) (value : JsonWithBytes.OrderedI64)
    (valid : value.WellFormed) (safe : KeysSatisfy NoDollar value) :
    ∃ restored : JsonWithBytes.OrderedI64,
      parseI64Text? profile .none (renderText (atprotoCodec profile) .none (embedI64 value)) = some restored ∧
      ∃ restoredValid : restored.WellFormed, restored.toJson restoredValid = value.toJson valid :=
  i64_text_roundtrip_unordered profile value valid (noDollar_noReserved _ safe)

theorem i64_textLanguage_iff (policy : Escape) (bytes : List UInt8) :
    bytes ∈ jsonWithBytesI64TextLanguage policy ↔
      ∃ value, AtprotoTextRep .any policy (Bytes.ofList bytes) value ∧ links value = [] := by
  change (parseI64Text? .any policy (Bytes.ofList bytes)).isSome ↔ _
  simp only [Option.isSome_iff_exists, parseI64Text_iff, linkFree_i64_iff]
  grind

end Silmaril.Formats.Cbor.Drisl.Debug
