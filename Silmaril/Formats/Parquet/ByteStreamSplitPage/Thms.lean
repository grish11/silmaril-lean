module

public import Silmaril.Formats.Parquet.ByteStreamSplitPage.Defs
import Silmaril.Proofs.Formats.Parquet.ByteStreamSplitPage.Correctness

/-! Schema width provenance, exact page and lane extents, and ordered slots. -/

public section

namespace Silmaril.Formats.Parquet.ByteStreamSplitPage

/-- The selected kind agrees with the leaf, including its declared fixed width. -/
theorem selectKind_sound {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {kind : ByteStreamSplit.Kind} (h : selectKind leaf physical = .ok kind) :
    Selection leaf physical kind :=
  Proofs.Formats.Parquet.ByteStreamSplitPage.selectKind_sound h

theorem decode_ok_iff {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {params : ScalarPage.Parameters} {limits : Limits} {source : Bytes} {result : Decoded} :
    decode leaf physical params limits source = .ok result ↔
      ∃ (page : ScalarPage.Prepared) (values : List result.kind.Value),
        selectKind leaf physical = .ok result.kind ∧
        ScalarPage.prepareFor 9 params limits.page source = .ok page ∧
        ByteStreamSplit.decode result.kind limits.scalars (page.mask.count true) page.scalars =
          .ok values ∧ result.slots.map Option.isSome = page.mask ∧ result.slots.filterMap id = values :=
  Proofs.Formats.Parquet.ByteStreamSplitPage.decode_ok_iff

/-- The checked scalar suffix splits into the exact lanes used by the ordered result. -/
theorem decode_wire_sound {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {params : ScalarPage.Parameters} {limits : Limits} {source : Bytes} {result : Decoded}
    (h : decode leaf physical params limits source = .ok result) :
    params.encoding = 9 ∧ Selection leaf physical result.kind ∧
      ∃ (layout : FlatPage.Layout) (page : ScalarPage.Prepared) (words : List (List UInt8)),
        ScalarPage.validateFor 9 params limits.page source = .ok layout ∧
        ScalarPage.PreparedWire params limits.page layout source page ∧
        ByteStreamSplit.Admission limits.scalars result.kind.width (page.mask.count true) page.scalars ∧
        ByteStreamSplit.LaneOrder result.kind.width (page.mask.count true) page.scalars words ∧
        result.slots.map Option.isSome = page.mask ∧
        result.slots.filterMap id = words.map result.kind.readWord :=
  Proofs.Formats.Parquet.ByteStreamSplitPage.decode_wire_sound h

theorem decode_counts {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {params : ScalarPage.Parameters} {limits : Limits} {source : Bytes} {result : Decoded}
    (h : decode leaf physical params limits source = .ok result) :
    result.slots.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (result.slots.filterMap id).length = params.numValues - nulls :=
  Proofs.Formats.Parquet.ByteStreamSplitPage.decode_counts h

end Silmaril.Formats.Parquet.ByteStreamSplitPage
