module

public import Silmaril.Formats.Parquet.DeltaPage.Defs
import Silmaril.Proofs.Formats.Parquet.DeltaPage.Correctness

/-! Physical dispatch, exact V1/V2 wire slices, and ordered nullable slots. -/

public section

namespace Silmaril.Formats.Parquet.DeltaPage

theorem kind_ofPhysical_ok_iff {physical : Footer.PhysicalType} {kind : Kind} :
    Kind.ofPhysical? physical = some kind ↔ physical = kind.physicalType :=
  Proofs.Formats.Parquet.DeltaPage.kind_ofPhysical_ok_iff

theorem encoding_ofId_ok_iff {kind : Kind} {id : Int} {encoding : Encoding kind} :
    Encoding.ofId? kind id = some encoding ↔ id = encoding.id :=
  Proofs.Formats.Parquet.DeltaPage.encoding_ofId_ok_iff

/-- The exact checked scalar suffix is decoded for the checked present count. -/
theorem decode_ok_iff {kind : Kind} {params : ScalarPage.Parameters} {limits : Limits}
    {source : Bytes} {output : List (Option kind.Value)} :
    decode kind params limits source = .ok output ↔
      ∃ (encoding : Encoding kind) (page : ScalarPage.Prepared) (values : List kind.Value),
        params.encoding = encoding.id ∧
        ScalarPage.prepareFor encoding.id params limits.page source = .ok page ∧
        encoding.read limits (page.mask.count true) page.scalars = .ok values ∧
        output.map Option.isSome = page.mask ∧ output.filterMap id = values :=
  Proofs.Formats.Parquet.DeltaPage.decode_ok_iff

/-- The selected V1 or V2 layout accounts for both declared byte extents. -/
theorem decode_wire_sound {kind : Kind} {params : ScalarPage.Parameters} {limits : Limits}
    {source : Bytes} {output : List (Option kind.Value)}
    (h : decode kind params limits source = .ok output) :
    ∃ (encoding : Encoding kind) (layout : FlatPage.Layout) (page : ScalarPage.Prepared)
        (values : List kind.Value),
      params.encoding = encoding.id ∧
      ScalarPage.validateFor encoding.id params limits.page source = .ok layout ∧
      ScalarPage.PreparedWire params limits.page layout source page ∧
      encoding.read limits (page.mask.count true) page.scalars = .ok values ∧
      output.map Option.isSome = page.mask ∧ output.filterMap id = values :=
  Proofs.Formats.Parquet.DeltaPage.decode_wire_sound h

theorem decode_counts {kind : Kind} {params : ScalarPage.Parameters} {limits : Limits}
    {source : Bytes} {output : List (Option kind.Value)}
    (h : decode kind params limits source = .ok output) :
    output.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (output.filterMap id).length = params.numValues - nulls :=
  Proofs.Formats.Parquet.DeltaPage.decode_counts h

end Silmaril.Formats.Parquet.DeltaPage
