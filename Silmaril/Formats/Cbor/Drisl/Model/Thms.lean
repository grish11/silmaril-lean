module

public import Silmaril.Formats.Cbor.Drisl.Model.Defs
public import Silmaril.Formats.Cbor.Drisl.Convert.Thms
public import Silmaril.Formats.Cbor.Drisl.Thms
import Silmaril.Proofs.Formats.Cbor.Drisl.Model

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

theorem drisl_dasl_language : drislCborLanguage .dasl = language .drislExactCid :=
  Silmaril.Proofs.Formats.Cbor.Drisl.Model.drisl_dasl_language

theorem drisl_bdasl_language : drislCborLanguage .bdasl = language .drislBdaslExactCid :=
  Silmaril.Proofs.Formats.Cbor.Drisl.Model.drisl_bdasl_language

theorem atproto_dasl_language : atprotoCborLanguage .dasl = language .atprotoCoreExactCid :=
  Silmaril.Proofs.Formats.Cbor.Drisl.Model.atproto_dasl_language

theorem atproto_bdasl_language : atprotoCborLanguage .bdasl =
    language { Profile.atprotoCoreExactCid with links := .bdasl } :=
  Silmaril.Proofs.Formats.Cbor.Drisl.Model.atproto_bdasl_language

/-- Every accepted canonical DRISL item is reprinted as exactly the input bytes. -/
theorem drisl_render_of_parse (profile : CidProfile) {bytes : List UInt8} {tree : Ordered (Cid profile)}
    (read : parseCbor? drislCbor (Cid.codec profile) bytes = some tree) :
    renderCbor? drislCbor (Cid.codec profile) tree = some bytes :=
  Silmaril.Proofs.Formats.Cbor.Drisl.Model.drisl_render_of_parse profile read

/-- Every accepted canonical ATProto DRISL item is reprinted as exactly the input bytes. -/
theorem atproto_render_of_parse (profile : CidProfile) {bytes : List UInt8} {tree : OrderedATProto (Cid profile)}
    (read : parseCbor? i64Cbor (Cid.codec profile) bytes = some tree) :
    renderCbor? i64Cbor (Cid.codec profile) tree = some bytes :=
  Silmaril.Proofs.Formats.Cbor.Drisl.Model.atproto_render_of_parse profile read

/-- Accepted ATProto bytes reprint unchanged when the link decoder preserves the input CID bytes. -/
theorem atproto_render_of_parse_with_codec {Link : Type} (cid : CidCodec Link)
    (reencodes : ∀ bytes link, cid.parse? bytes = some link → cid.bytes link = bytes)
    {bytes : List UInt8} {tree : OrderedATProto Link}
    (read : parseCbor? i64Cbor cid bytes = some tree) : renderCbor? i64Cbor cid tree = some bytes :=
  Silmaril.Proofs.Formats.Cbor.Drisl.Model.atproto_render_of_parse_with_codec cid reencodes read

/-- On encodable, recursively key-sorted DRISL trees the writer and reader preserve the exact AST. -/
theorem drisl_ordered_roundtrip (profile : CidProfile) (tree : Ordered (Cid profile))
    (encodable : (emitModel drislCbor (Cid.codec profile) false tree).Encodable)
    (order : canonicalMaps (emitModel drislCbor (Cid.codec profile) false tree) = true) :
    let bytes := (emitModel drislCbor (Cid.codec profile) false tree).encode
    renderCbor? drislCbor (Cid.codec profile) tree = some bytes ∧
      parseCbor? drislCbor (Cid.codec profile) bytes = some tree :=
  Silmaril.Proofs.Formats.Cbor.Drisl.Model.drisl_ordered_roundtrip profile tree encodable order

/-- On encodable, recursively key-sorted ATProto trees the writer and reader preserve the exact AST. -/
theorem atproto_ordered_roundtrip (profile : CidProfile) (tree : OrderedATProto (Cid profile))
    (encodable : (emitModel i64Cbor (Cid.codec profile) false tree).Encodable)
    (order : canonicalMaps (emitModel i64Cbor (Cid.codec profile) false tree) = true) :
    let bytes := (emitModel i64Cbor (Cid.codec profile) false tree).encode
    renderCbor? i64Cbor (Cid.codec profile) tree = some bytes ∧
      parseCbor? i64Cbor (Cid.codec profile) bytes = some tree :=
  Silmaril.Proofs.Formats.Cbor.Drisl.Model.atproto_ordered_roundtrip profile tree encodable order

/-- Ordered encoding needs the CID inverse only on links actually used by the tree. -/
theorem atproto_ordered_roundtrip_with_codec {Link : Type} (cid : CidCodec Link) (tree : OrderedATProto Link)
    (readCid : ∀ link ∈ links tree, cid.parse? (cid.bytes link) = some link)
    (encodable : (emitModel i64Cbor cid false tree).Encodable)
    (order : canonicalMaps (emitModel i64Cbor cid false tree) = true) :
    let bytes := (emitModel i64Cbor cid false tree).encode
    renderCbor? i64Cbor cid tree = some bytes ∧ parseCbor? i64Cbor cid bytes = some tree :=
  Silmaril.Proofs.Formats.Cbor.Drisl.Model.atproto_ordered_roundtrip_with_codec cid tree readCid encodable order

theorem parseCbor_eq_some_iff {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)
    {bytes : List UInt8} {tree : RawJson (Scalar Numeric Link)} :
    parseCbor? numeric cid bytes = some tree ↔
      ∃ value, Cbor.decode bytes = some value ∧ value.encode = bytes ∧ canonicalMaps value = true ∧
        interpretCbor? numeric cid value = some tree := by
  change (Cbor.decode bytes).bind _ = _ ↔ _
  simp [Option.bind_eq_some_iff, ite_eq_iff, and_assoc]

theorem canonicalCbor_iff {Numeric Link : Type} (numeric : CborCodec Numeric) (cid : CidCodec Link)
    (bytes : List UInt8) : bytes ∈ canonicalCbor numeric cid ↔
      ∃ value ∈ cborValues numeric cid,
        Cbor.decode bytes = some value ∧ value.encode = bytes ∧ canonicalMaps value = true := by
  change (parseCbor? numeric cid bytes).isSome ↔ _
  simp only [Option.isSome_iff_exists, parseCbor_eq_some_iff, cborValues, Set.mem_ofPred_eq]
  grind

theorem interpretI64Cbor_iff (profile : CidProfile) (value : Value) (tree : JsonWithBytes.OrderedI64) :
    interpretI64Cbor? profile value = some tree ↔
      interpretCbor? i64Cbor (Cid.codec profile) value = some (embedI64 tree) :=
  restrictToI64_iff _ tree

theorem i64_values_iff (value : Value) : value ∈ i64WithBytesValues ↔
    ∃ tree, interpretCbor? i64Cbor (Cid.codec .any) value = some tree ∧ links tree = [] := by
  change (interpretI64Cbor? .any value).isSome ↔ _
  simp only [Option.isSome_iff_exists, interpretI64Cbor_iff, linkFree_i64_iff]
  grind

theorem parseI64Cbor_iff (profile : CidProfile) (bytes : List UInt8) (tree : JsonWithBytes.OrderedI64) :
    parseI64Cbor? profile bytes = some tree ↔ parseCbor? i64Cbor (Cid.codec profile) bytes = some (embedI64 tree) :=
  restrictToI64_iff _ tree

theorem i64_cborLanguage_iff (bytes : List UInt8) : bytes ∈ i64WithBytesCborLanguage ↔
    ∃ value, parseCbor? i64Cbor (Cid.codec .any) bytes = some value ∧ links value = [] := by
  change (parseI64Cbor? .any bytes).isSome ↔ _
  simp only [Option.isSome_iff_exists, parseI64Cbor_iff, linkFree_i64_iff]
  grind

section Examples

private def prefixedCid : List UInt8 :=
  (Value.tag 42 (.bytes ([0, 1, 0x55, 0x12, 32] ++ List.replicate 33 0))).encode

example : prefixedCid ∈ language .drislCidPrefix ∧ prefixedCid ∉ drislCborLanguage .dasl :=
  ⟨by decide +kernel, fun mem => by rw [drisl_dasl_language] at mem; exact (by decide +kernel : _ ∉ _) mem⟩

private def multiByteCodecCid : List UInt8 :=
  (Value.tag 42 (.bytes ([0, 1, 0xA9, 0x02, 0x12, 32] ++ List.replicate 32 0))).encode

example : multiByteCodecCid ∈ drislCborLanguage .any := by
  change (parseCbor? drislCbor (Cid.codec .any) multiByteCodecCid).isSome = true
  decide +kernel

example : multiByteCodecCid ∉ language .drislBdaslExactCid := by decide +kernel

example : (Value.uint (2 ^ 63)).encode ∈ language .drislNoFloatsExactCid ∧
    (Value.uint (2 ^ 63)).encode ∉ atprotoCborLanguage .dasl := by
  rw [atproto_dasl_language]
  exact ⟨by decide +kernel, by decide +kernel⟩

end Examples

end Silmaril.Formats.Cbor.Drisl
