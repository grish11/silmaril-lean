module

public import Silmaril.Formats.Parquet.DeltaFixedPage.Defs
import Silmaril.Formats.Parquet.DeltaByteArray.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Init.Data.List.Nat.Sum
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.DeltaFixedPage

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.DeltaFixedPage

public theorem selectWidth_sound {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {width : Nat} (h : selectWidth leaf physical = .ok width) : WidthFor leaf physical width := by
  unfold selectWidth at h
  split at h
  · contradiction
  · rename_i shape
    simp only [not_or, not_not] at shape
    cases declared : leaf.typeLength with
    | none => rw [declared] at h; contradiction
    | some signed =>
      rw [declared] at h
      by_cases valid : 0 < signed ∧ signed < (DeltaByteArray.valueLengthLimit : Int)
      · simp only [ite_eq_left valid] at h
        cases h
        exact ⟨shape.1, shape.2.1, shape.2.2,
          declared.trans (congrArg some (Int.toNat_of_nonneg (by omega : 0 ≤ signed)).symm),
          by omega, by omega⟩
      · simp [valid] at h

private theorem mapError_ok_iff {ε δ α : Type} {action : Except ε α} {f : ε → δ} {value : α} :
    action.mapError f = .ok value ↔ action = .ok value := by
  cases action <;> simp [Except.mapError]

private theorem bind_ok_iff {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} :
    (action >>= next) = .ok output ↔
      ∃ input, action = .ok input ∧ next input = .ok output := by
  cases action <;> simp [Bind.bind, Except.bind]

public theorem readValues_ok_iff {width expected : Nat} {limits : DeltaByteArray.Limits}
    {source : Bytes} {values : List Bytes} :
    readValues width expected limits source = .ok values ↔
      0 < width ∧ width < DeltaByteArray.valueLengthLimit ∧ width ≤ limits.valueBytes ∧
      expected * width ≤ limits.decodedBytes ∧
      DeltaByteArray.decode (limitsForWidth width limits) expected source = .ok values ∧
      (∀ value ∈ values, value.length = width) := by
  unfold readValues
  by_cases valid : 0 < width ∧ width < DeltaByteArray.valueLengthLimit
  · by_cases widthCap : width ≤ limits.valueBytes
    · by_cases totalCap : expected * width ≤ limits.decodedBytes
      · simp only [ite_eq_left valid, ite_eq_right (Nat.not_lt.mpr widthCap),
          ite_eq_right (Nat.not_lt.mpr totalCap)]
        constructor
        · intro h
          obtain ⟨read, decoded, verified⟩ := bind_ok_iff.mp h
          split at verified
          · rename_i widths
            cases verified
            exact ⟨valid.1, valid.2, widthCap, totalCap, mapError_ok_iff.mp decoded,
              fun value member => by simpa using List.all_eq_true.mp widths value member⟩
          · contradiction
        · rintro ⟨_, _, _, _, decoded, widths⟩
          refine bind_ok_iff.mpr ⟨values, mapError_ok_iff.mpr decoded, ?_⟩
          have every : values.all (fun value => value.length == width) = true :=
            List.all_eq_true.mpr (fun value member => by simpa using widths value member)
          simp only [ite_eq_left every]
          rfl
      · simp [valid, Nat.not_lt.mpr widthCap, Nat.lt_of_not_ge totalCap, totalCap]
    · simp [valid, Nat.lt_of_not_ge widthCap, widthCap]
  · simp only [ite_eq_right valid]
    constructor
    · intro h
      contradiction
    · rintro ⟨positive, bounded, _⟩
      exact (valid ⟨positive, bounded⟩).elim

public theorem readValues_sound {width expected : Nat} {limits : DeltaByteArray.Limits}
    {source : Bytes} {values : List Bytes}
    (h : readValues width expected limits source = .ok values) :
    ValuesWire width expected limits source values := by
  obtain ⟨_, _, widthCap, _, decoded, widths⟩ := readValues_ok_iff.mp h
  obtain ⟨prefixStream, suffixStream, payload, suffixes, _, whole, consumed, prefixValid,
    suffixValid, assembled, first, reconstructed, count, _⟩ := DeltaByteArray.decode_sound decoded
  have mapped : values.map Bytes.length = values.map (fun _ => width) :=
    List.map_congr_left widths
  refine ⟨count, widths, ?_, prefixStream, suffixStream, payload, suffixes, whole, consumed,
    prefixValid, suffixValid, assembled, first, ?_⟩
  · rw [mapped, List.map_const', List.sum_replicate_nat, count]
  · simpa [limitsForWidth, Nat.min_eq_left widthCap] using reconstructed

public theorem decode_ok_iff {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {params : ScalarPage.Parameters} {limits : Limits} {source : Bytes}
    {output : List (Option Bytes)} :
    decode leaf physical params limits source = .ok output ↔
      ∃ (width : Nat) (page : ScalarPage.Prepared) (values : List Bytes),
        selectWidth leaf physical = .ok width ∧
        ScalarPage.prepareFor 7 params limits.page source = .ok page ∧
        readValues width (page.mask.count true) limits.values page.scalars = .ok values ∧
        output.map Option.isSome = page.mask ∧ output.filterMap id = values := by
  unfold decode
  constructor
  · intro h
    obtain ⟨width, selected, h⟩ := bind_ok_iff.mp h
    obtain ⟨page, prepared, h⟩ := bind_ok_iff.mp h
    obtain ⟨values, read, rebuilt⟩ := bind_ok_iff.mp h
    exact ⟨width, page, values, selected, mapError_ok_iff.mp prepared, read,
      FlatPage.reconstruct_ok_iff.mp (mapError_ok_iff.mp rebuilt)⟩
  · rintro ⟨width, page, values, selected, prepared, read, shape, order⟩
    refine bind_ok_iff.mpr ⟨width, selected, ?_⟩
    refine bind_ok_iff.mpr ⟨page, mapError_ok_iff.mpr prepared, ?_⟩
    exact bind_ok_iff.mpr ⟨values, read, mapError_ok_iff.mpr
      (FlatPage.reconstruct_ok_iff.mpr ⟨shape, order⟩)⟩

public theorem decode_wire_sound {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {params : ScalarPage.Parameters} {limits : Limits} {source : Bytes} {output : List (Option Bytes)}
    (h : decode leaf physical params limits source = .ok output) :
    params.encoding = 7 ∧
      ∃ (width : Nat) (layout : FlatPage.Layout) (page : ScalarPage.Prepared),
        WidthFor leaf physical width ∧
        ScalarPage.validateFor 7 params limits.page source = .ok layout ∧
        ScalarPage.PreparedWire params limits.page layout source page ∧
        output.map Option.isSome = page.mask ∧
        ValuesWire width (page.mask.count true) limits.values page.scalars (output.filterMap id) := by
  obtain ⟨width, page, values, selected, prepared, read, shape, order⟩ := decode_ok_iff.mp h
  obtain ⟨layout, valid, wire⟩ := ScalarPage.prepareFor_sound prepared
  have encoding : params.encoding = 7 := by
    by_contra unequal
    simp [ScalarPage.validateFor, unequal] at valid
  rw [order]
  exact ⟨encoding, width, layout, page, selectWidth_sound selected, valid, wire, shape, readValues_sound read⟩

public theorem decode_counts {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {params : ScalarPage.Parameters} {limits : Limits} {source : Bytes} {output : List (Option Bytes)}
    (h : decode leaf physical params limits source = .ok output) :
    output.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (output.filterMap id).length = params.numValues - nulls := by
  obtain ⟨_, page, values, _, prepared, read, shape, order⟩ := decode_ok_iff.mp h
  obtain ⟨total, present⟩ := ScalarPage.preparedFor_counts prepared
  refine ⟨by simpa [total] using congrArg List.length shape, ?_⟩
  cases version : params.version with
  | v1 => trivial
  | v2 =>
    rw [version] at present
    rw [order, (readValues_sound read).count, present]

end Silmaril.Proofs.Formats.Parquet.DeltaFixedPage
