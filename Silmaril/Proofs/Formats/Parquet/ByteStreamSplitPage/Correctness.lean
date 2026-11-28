module

public import Silmaril.Formats.Parquet.ByteStreamSplitPage.Defs
import Silmaril.Formats.Parquet.ByteStreamSplit.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms
import Init.Omega

namespace Silmaril.Proofs.Formats.Parquet.ByteStreamSplitPage

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.ByteStreamSplitPage

public theorem selectKind_sound {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {kind : ByteStreamSplit.Kind} (h : selectKind leaf physical = .ok kind) :
    Selection leaf physical kind := by
  unfold selectKind at h
  split at h
  · contradiction
  · rename_i agrees
    simp only [not_or, not_not] at agrees
    refine ⟨agrees.1, agrees.2, ?_⟩
    cases physical with
    | int32 => cases h; exact .int32
    | int64 => cases h; exact .int64
    | float => cases h; exact .float
    | double => cases h; exact .double
    | fixedLenByteArray =>
      cases declared : leaf.typeLength with
      | none => rw [declared] at h; contradiction
      | some width =>
        rw [declared] at h
        change (if 0 < width ∧ width < (ByteStreamSplit.signedSizeLimit : Int)
          then Except.ok (ByteStreamSplit.Kind.fixedLenBytes width.toNat)
          else .error Error.invalidFixedWidth) = .ok kind at h
        by_cases admitted : 0 < width ∧ width < (ByteStreamSplit.signedSizeLimit : Int)
        · rw [ite_eq_left admitted] at h
          cases h
          exact .fixed (congrArg some (Int.toNat_of_nonneg (by omega : 0 ≤ width)).symm)
            (by omega) (by omega)
        · rw [ite_eq_right admitted] at h
          contradiction
    | boolean | int96 | byteArray => contradiction

private theorem mapError_ok_iff {ε δ α : Type} {action : Except ε α} {f : ε → δ} {value : α} :
    action.mapError f = .ok value ↔ action = .ok value := by
  cases action <;> simp [Except.mapError]

private theorem bind_ok_iff {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} :
    (action >>= next) = .ok output ↔
      ∃ input, action = .ok input ∧ next input = .ok output := by
  cases action <;> simp [Bind.bind, Except.bind]

private theorem validate_encoding {params : ScalarPage.Parameters} {limits : ScalarPage.Limits}
    {source : Bytes} {layout : FlatPage.Layout}
    (h : ScalarPage.validateFor 9 params limits source = .ok layout) : params.encoding = 9 := by
  simp only [ScalarPage.validateFor] at h
  split at h
  · contradiction
  · rename_i encoding
    exact not_not.mp encoding

public theorem decode_ok_iff {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {params : ScalarPage.Parameters} {limits : Limits} {source : Bytes} {result : Decoded} :
    decode leaf physical params limits source = .ok result ↔
      ∃ (page : ScalarPage.Prepared) (values : List result.kind.Value),
        selectKind leaf physical = .ok result.kind ∧
        ScalarPage.prepareFor 9 params limits.page source = .ok page ∧
        ByteStreamSplit.decode result.kind limits.scalars (page.mask.count true) page.scalars =
          .ok values ∧ result.slots.map Option.isSome = page.mask ∧ result.slots.filterMap id = values := by
  unfold decode
  constructor
  · intro h
    obtain ⟨kind, selected, h⟩ := bind_ok_iff.mp h
    obtain ⟨page, prepared, h⟩ := bind_ok_iff.mp h
    obtain ⟨values, read, h⟩ := bind_ok_iff.mp h
    obtain ⟨slots, rebuilt, h⟩ := bind_ok_iff.mp h
    cases h
    obtain ⟨shape, order⟩ := FlatPage.reconstruct_ok_iff.mp (mapError_ok_iff.mp rebuilt)
    exact ⟨page, values, selected, mapError_ok_iff.mp prepared, mapError_ok_iff.mp read, shape, order⟩
  · rintro ⟨page, values, selected, prepared, read, shape, order⟩
    refine bind_ok_iff.mpr ⟨result.kind, selected, ?_⟩
    refine bind_ok_iff.mpr ⟨page, mapError_ok_iff.mpr prepared, ?_⟩
    refine bind_ok_iff.mpr ⟨values, mapError_ok_iff.mpr read, ?_⟩
    refine bind_ok_iff.mpr ⟨result.slots, mapError_ok_iff.mpr ?_, rfl⟩
    exact FlatPage.reconstruct_ok_iff.mpr ⟨shape, order⟩

public theorem decode_wire_sound {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {params : ScalarPage.Parameters} {limits : Limits} {source : Bytes} {result : Decoded}
    (h : decode leaf physical params limits source = .ok result) :
    params.encoding = 9 ∧ Selection leaf physical result.kind ∧
      ∃ (layout : FlatPage.Layout) (page : ScalarPage.Prepared) (words : List (List UInt8)),
        ScalarPage.validateFor 9 params limits.page source = .ok layout ∧
        ScalarPage.PreparedWire params limits.page layout source page ∧
        ByteStreamSplit.Admission limits.scalars result.kind.width (page.mask.count true) page.scalars ∧
        ByteStreamSplit.LaneOrder result.kind.width (page.mask.count true) page.scalars words ∧
        result.slots.map Option.isSome = page.mask ∧
        result.slots.filterMap id = words.map result.kind.readWord := by
  obtain ⟨page, values, selected, prepared, read, shape, order⟩ := decode_ok_iff.mp h
  obtain ⟨layout, valid, wire⟩ := ScalarPage.prepareFor_sound prepared
  obtain ⟨words, admitted, lanes, typed, _⟩ := ByteStreamSplit.decode_sound read
  exact ⟨validate_encoding valid, selectKind_sound selected,
    layout, page, words, valid, wire, admitted, lanes, shape, order.trans typed⟩

public theorem decode_counts {leaf : Footer.SchemaElement} {physical : Footer.PhysicalType}
    {params : ScalarPage.Parameters} {limits : Limits} {source : Bytes} {result : Decoded}
    (h : decode leaf physical params limits source = .ok result) :
    result.slots.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (result.slots.filterMap id).length = params.numValues - nulls := by
  obtain ⟨page, values, _, prepared, _, shape, order⟩ := decode_ok_iff.mp h
  obtain ⟨length, counts⟩ := ScalarPage.preparedFor_counts prepared
  refine ⟨?_, ?_⟩
  · have slots := congrArg List.length shape
    rwa [List.length_map, length] at slots
  · have reconstructed := FlatPage.reconstruct_ok_iff.mpr ⟨shape, order⟩
    have present := (FlatPage.reconstruct_exists_iff page.mask values).mp ⟨result.slots, reconstructed⟩
    cases version : params.version with
    | v1 => trivial
    | v2 =>
      rw [version] at counts
      rw [order, ← present]
      exact counts

end Silmaril.Proofs.Formats.Parquet.ByteStreamSplitPage
