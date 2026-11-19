module

public import Silmaril.Formats.Cbor.Drisl.Debug.Text.Defs
public import Silmaril.Formats.Cbor.Drisl.Number.Thms
public import Silmaril.Formats.JsonWire.Thms
public import Silmaril.Formats.JsonWithBytes.Traverse.Thms

@[expose] public section

namespace Silmaril.Proofs.Formats.Cbor.Drisl.DebugText

open Silmaril.Formats Silmaril.Formats.Cbor.Drisl Silmaril.Formats.Cbor.Drisl.Debug

theorem textLanguage_le_json {Input Link : Type} (codec : Codec Input JsonWire.Decimal Link)
    (policy : Escape) : textLanguage codec policy ≤ JsonBytes.language .rfc8259 := by
  intro bytes accepted
  apply (JsonWire.parse?_isSome_iff bytes).mp
  change (parseText? codec policy (Bytes.ofList bytes)).isSome = true at accepted
  cases parsed : JsonWire.parse? (Bytes.ofList bytes) with
  | none => simp [parseText?, parsed] at accepted
  | some => simp

theorem atproto_agrees {index : JsonIx} (profile : CidProfile) (policy : Escape)
    (value : RawSyn String (JsonWithBytes.Scalar Int64) index) :
    encode (atprotoCodec profile) policy (value.mapScalar Scalar.data) =
      encode jsonWithBytesI64Codec policy (value.mapScalar Scalar.data) := by
  induction value with
  | scalar value => cases value <;> rfl
  | list _ ih | map _ ih => simp [encode, ih]
  | nil | objNil => rfl
  | cons _ _ ih tailIH | objCons _ _ _ ih tailIH => simp [encode, ih, tailIH]

theorem drisl_agrees {index : JsonIx} (profile : CidProfile) (policy : Escape)
    (value : RawSyn String (Scalar Int64 (Cid profile)) index) :
    encode (drislCodec profile) policy (value.mapScalar widenScalar) = encode (atprotoCodec profile) policy value := by
  induction value with
  | scalar value =>
    cases value with
    | data atom => cases atom <;> simp [encode, widenScalar, drislCodec, atprotoCodec, Codec.withCid,
        Number.toDecimal, Integer.toInt_ofInt64, Function.comp_def]
    | link => rfl
  | list _ ih | map _ ih => simp [encode, ih]
  | nil | objNil => rfl
  | cons _ _ ih tailIH | objCons _ _ _ ih tailIH => simp [encode, ih, tailIH]

theorem parse_eq_some_iff {Input Link : Type} (codec : Codec Input JsonWire.Decimal Link)
    (policy : Escape) {bytes : Bytes} {value : RawJson (Scalar Input Link)} :
    parseText? codec policy bytes = some value ↔ value.WellFormed ∧
      ∃ source tree, JsonWire.parse? bytes = some source ∧ ofWire? source = some tree ∧
        decode? codec policy tree = some value := by
  change ((JsonWire.parse? bytes).bind fun source => (ofWire? source).bind fun tree =>
    (decode? codec policy tree).bind fun output => if JsonWithBytes.uniqueKeys output then some output else none) =
    some value ↔ _
  simp only [Option.bind_eq_some_iff, ite_eq_iff, Option.some.injEq, reduceCtorEq, and_false, or_false]
  constructor
  · rintro ⟨source, parsed, tree, lifted, _, decoded, hit, rfl⟩
    exact ⟨(JsonWithBytes.uniqueKeys_iff _).mp hit, source, tree, parsed, lifted, decoded⟩
  · rintro ⟨valid, source, tree, parsed, lifted, decoded⟩
    exact ⟨source, parsed, tree, lifted, value, decoded, (JsonWithBytes.uniqueKeys_iff _).mpr valid, rfl⟩

end Silmaril.Proofs.Formats.Cbor.Drisl.DebugText
