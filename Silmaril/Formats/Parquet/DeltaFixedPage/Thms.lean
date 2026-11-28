module

public import Silmaril.Formats.Parquet.DeltaFixedPage.Defs
import Silmaril.Proofs.Formats.Parquet.DeltaFixedPage.Correctness

/-! Schema-width provenance, exact scalar consumption, and ordered page slots. -/

public section

namespace Silmaril.Formats.Parquet.DeltaFixedPage

theorem selectWidth_sound {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {width : Nat} (h : selectWidth leaf physical = .ok width) : WidthFor leaf physical width :=
  Proofs.Formats.Parquet.DeltaFixedPage.selectWidth_sound h

/-- Admission checks the signed width range, budgets, exact delta decode, and
equality to the declared width for every returned value. -/
theorem readValues_ok_iff {width expected : Nat} {limits : DeltaByteArray.Limits}
    {source : Bytes} {values : List Bytes} :
    readValues width expected limits source = .ok values ↔
      0 < width ∧ width < DeltaByteArray.valueLengthLimit ∧ width ≤ limits.valueBytes ∧
      expected * width ≤ limits.decodedBytes ∧
      DeltaByteArray.decode (limitsForWidth width limits) expected source = .ok values ∧
      (∀ value ∈ values, value.length = width) :=
  Proofs.Formats.Parquet.DeltaFixedPage.readValues_ok_iff

/-- The two length streams and the concatenated suffixes account for the
entire scalar slice. Reconstructed values consume exactly count times width. -/
theorem readValues_sound {width expected : Nat} {limits : DeltaByteArray.Limits}
    {source : Bytes} {values : List Bytes}
    (h : readValues width expected limits source = .ok values) :
    ValuesWire width expected limits source values :=
  Proofs.Formats.Parquet.DeltaFixedPage.readValues_sound h

theorem decode_ok_iff {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {params : ScalarPage.Parameters} {limits : Limits} {source : Bytes}
    {output : List (Option Bytes)} :
    decode leaf physical params limits source = .ok output ↔
      ∃ (width : Nat) (page : ScalarPage.Prepared) (values : List Bytes),
        selectWidth leaf physical = .ok width ∧
        ScalarPage.prepareFor 7 params limits.page source = .ok page ∧
        readValues width (page.mask.count true) limits.values page.scalars = .ok values ∧
        output.map Option.isSome = page.mask ∧ output.filterMap id = values :=
  Proofs.Formats.Parquet.DeltaFixedPage.decode_ok_iff

/-- Successful V1/V2 pages bind raw tag 7, the schema width, their exact
on-disk framing, and ordered fixed-width values under the checked mask. -/
theorem decode_wire_sound {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {params : ScalarPage.Parameters} {limits : Limits} {source : Bytes} {output : List (Option Bytes)}
    (h : decode leaf physical params limits source = .ok output) :
    params.encoding = 7 ∧
      ∃ (width : Nat) (layout : FlatPage.Layout) (page : ScalarPage.Prepared),
        WidthFor leaf physical width ∧
        ScalarPage.validateFor 7 params limits.page source = .ok layout ∧
        ScalarPage.PreparedWire params limits.page layout source page ∧
        output.map Option.isSome = page.mask ∧
        ValuesWire width (page.mask.count true) limits.values page.scalars (output.filterMap id) :=
  Proofs.Formats.Parquet.DeltaFixedPage.decode_wire_sound h

theorem decode_counts {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {params : ScalarPage.Parameters} {limits : Limits} {source : Bytes} {output : List (Option Bytes)}
    (h : decode leaf physical params limits source = .ok output) :
    output.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (output.filterMap id).length = params.numValues - nulls :=
  Proofs.Formats.Parquet.DeltaFixedPage.decode_counts h

end Silmaril.Formats.Parquet.DeltaFixedPage
