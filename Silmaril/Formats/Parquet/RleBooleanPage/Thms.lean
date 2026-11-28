module

public import Silmaril.Formats.Parquet.RleBooleanPage.Defs
import Silmaril.Proofs.Formats.Parquet.RleBooleanPage.Correctness

/-! Exact RLE value framing, checked V1/V2 layout, and ordered nullable slots. -/

public section

namespace Silmaril.Formats.Parquet.RleBooleanPage

/-- Accepted scalars have one exact little-endian length word and a width-one
hybrid stream that consumes the entire payload. -/
theorem readValues_ok_iff {expected : Nat} {limits : Hybrid.Limits}
    {source : Bytes} {values : List Bool} :
    readValues expected limits source = .ok values ↔ ValuesWire expected limits source values :=
  Proofs.Formats.Parquet.RleBooleanPage.readValues_ok_iff

theorem readValues_length {expected : Nat} {limits : Hybrid.Limits}
    {source : Bytes} {values : List Bool} (h : readValues expected limits source = .ok values) :
    values.length = expected :=
  Proofs.Formats.Parquet.RleBooleanPage.readValues_length h

/-- Validity recovers the original mask, and removing absent slots recovers
the decoded Boolean values in order. -/
theorem decode_ok_iff {physical : Footer.PhysicalType} {params : ScalarPage.Parameters}
    {limits : Limits} {source : Bytes} {output : List (Option Bool)} :
    decode physical params limits source = .ok output ↔
      physical = .boolean ∧ ∃ (page : ScalarPage.Prepared) (values : List Bool),
        ScalarPage.prepareFor 3 params limits.page source = .ok page ∧
        readValues (page.mask.count true) limits.values page.scalars = .ok values ∧
        output.map Option.isSome = page.mask ∧ output.filterMap id = values :=
  Proofs.Formats.Parquet.RleBooleanPage.decode_ok_iff

/-- Successful pages select BOOLEAN and raw encoding 3, with exact page
slices and exact scalar wire consumption. -/
theorem decode_wire_sound {physical : Footer.PhysicalType} {params : ScalarPage.Parameters}
    {limits : Limits} {source : Bytes} {output : List (Option Bool)}
    (h : decode physical params limits source = .ok output) :
    physical = .boolean ∧ params.encoding = 3 ∧
      ∃ (layout : FlatPage.Layout) (page : ScalarPage.Prepared),
        ScalarPage.validateFor 3 params limits.page source = .ok layout ∧
        ScalarPage.PreparedWire params limits.page layout source page ∧
        output.map Option.isSome = page.mask ∧
        ValuesWire (page.mask.count true) limits.values page.scalars (output.filterMap id) :=
  Proofs.Formats.Parquet.RleBooleanPage.decode_wire_sound h

/-- Every input slot is represented, and the V2 header agrees with the number
of present Booleans. In both versions the checked mask supplies that count. -/
theorem decode_counts {physical : Footer.PhysicalType} {params : ScalarPage.Parameters}
    {limits : Limits} {source : Bytes} {output : List (Option Bool)}
    (h : decode physical params limits source = .ok output) :
    output.length = params.numValues ∧
      (output.filterMap id).length = (output.map Option.isSome).count true ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (output.filterMap id).length = params.numValues - nulls :=
  Proofs.Formats.Parquet.RleBooleanPage.decode_counts h

end Silmaril.Formats.Parquet.RleBooleanPage
