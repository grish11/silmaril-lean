module

public import Silmaril.Formats.Parquet.LegacyBitPackedV1.Defs
import Silmaril.Proofs.Formats.Parquet.LegacyBitPackedV1.Correctness

/-! Exact legacy level and PLAIN value extents, slot order, and null counts. -/

public section

namespace Silmaril.Formats.Parquet.LegacyBitPackedV1

theorem admit_sound {physical : Footer.PhysicalType} {schema : FlatPage.LevelSchema}
    {codec : Int} {header : Page.Header} {info : Page.DataV1}
    (h : admit physical schema codec header = .ok info) : Profile physical schema codec header info :=
  Proofs.Formats.Parquet.LegacyBitPackedV1.admit_sound h

/-- The checked definition prefix and the exact untouched PLAIN suffix account
for the entire admitted on-disk body. -/
theorem prepare_sound {physical : Footer.PhysicalType} {schema : FlatPage.LevelSchema}
    {codec : Int} {header : Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {page : Prepared} (h : prepare physical schema codec header limits body = .ok page) :
    ∃ info, Profile physical schema codec header info ∧ PreparedWire header info limits body page :=
  Proofs.Formats.Parquet.LegacyBitPackedV1.prepare_sound h

theorem decode_ok_iff {physical : Footer.PhysicalType} {schema : FlatPage.LevelSchema}
    {codec : Int} {header : Page.Header} {limits : ScalarPage.Limits} {body : Bytes} {result : Decoded} :
    decodeInt32 physical schema codec header limits body = .ok result ↔
      ∃ (page : Prepared) (values : List Int32),
        prepare physical schema codec header limits body = .ok page ∧
        Plain.decodeInt32 (page.mask.count true) page.values = .ok values ∧
        result.slots.map Option.isSome = page.mask ∧ result.slots.filterMap id = values ∧
        result.nullCount = page.mask.count false :=
  Proofs.Formats.Parquet.LegacyBitPackedV1.decode_ok_iff

/-- Each checked level contributes a slot. The defined slots are precisely
the consecutive PLAIN words from the exact suffix, in wire order. -/
theorem decode_wire_sound {physical : Footer.PhysicalType} {schema : FlatPage.LevelSchema}
    {codec : Int} {header : Page.Header} {limits : ScalarPage.Limits} {body : Bytes} {result : Decoded}
    (h : decodeInt32 physical schema codec header limits body = .ok result) :
    ∃ (info : Page.DataV1) (page : Prepared) (words : List (List UInt8)),
      Profile physical schema codec header info ∧ PreparedWire header info limits body page ∧
      page.values.toList = words.flatten ∧ words.length = page.levels.count 1 ∧
      (∀ word ∈ words, word.length = 4) ∧ result.slots.map Option.isSome = page.mask ∧
      result.slots.filterMap id = words.map (fun word => (Plain.readUInt32Word word).toInt32) ∧
      result.nullCount = page.levels.count 0 :=
  Proofs.Formats.Parquet.LegacyBitPackedV1.decode_wire_sound h

/-- The definition levels determine the V1 null count, with one slot per
header value. -/
theorem decode_counts {physical : Footer.PhysicalType} {schema : FlatPage.LevelSchema}
    {codec : Int} {header : Page.Header} {limits : ScalarPage.Limits} {body : Bytes} {result : Decoded}
    (h : decodeInt32 physical schema codec header limits body = .ok result) :
    ∃ info : Page.DataV1, header.kind = .dataV1 info ∧ result.slots.length = info.numValues ∧
      result.nullCount = result.slots.countP Option.isNone ∧
      result.nullCount = info.numValues - (result.slots.filterMap id).length :=
  Proofs.Formats.Parquet.LegacyBitPackedV1.decode_counts h

end Silmaril.Formats.Parquet.LegacyBitPackedV1
