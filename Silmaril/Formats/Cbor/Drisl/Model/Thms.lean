module

public import Silmaril.Formats.Cbor.Drisl.Model.Defs
public import Silmaril.Formats.Cbor.Drisl.Convert.Thms

@[expose] public section

namespace Silmaril.Formats.Cbor.Drisl

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

theorem parseI64Cbor_iff (profile : CidProfile) (bytes : List UInt8) (tree : JsonWithBytes.OrderedI64) :
    parseI64Cbor? profile bytes = some tree ↔ parseCbor? i64Cbor (Cid.codec profile) bytes = some (embedI64 tree) :=
  restrictToI64_iff _ tree

theorem i64_cborLanguage_iff (bytes : List UInt8) : bytes ∈ i64WithBytesCborLanguage ↔
    ∃ value, parseCbor? i64Cbor (Cid.codec .any) bytes = some value ∧ links value = [] := by
  change (parseI64Cbor? .any bytes).isSome ↔ _
  simp only [Option.isSome_iff_exists, parseI64Cbor_iff, linkFree_i64_iff]
  grind

end Silmaril.Formats.Cbor.Drisl
