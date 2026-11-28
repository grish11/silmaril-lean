module

public import Silmaril.Formats.Parquet.DeltaPage.Defs
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.ScalarPage.Thms

namespace Silmaril.Proofs.Formats.Parquet.DeltaPage

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.DeltaPage

public theorem kind_ofPhysical_ok_iff {physical : Footer.PhysicalType} {kind : Kind} :
    Kind.ofPhysical? physical = some kind ↔ physical = kind.physicalType := by
  cases kind with
  | signed signed => cases signed <;> cases physical <;> simp [Kind.ofPhysical?, Kind.physicalType]
  | byteArray => cases physical <;> simp [Kind.ofPhysical?, Kind.physicalType]

public theorem encoding_ofId_ok_iff {kind : Kind} {id : Int} {encoding : Encoding kind} :
    Encoding.ofId? kind id = some encoding ↔ id = encoding.id := by
  cases encoding with
  | binaryPacked physical =>
    by_cases valid : id = 5 <;> simp [Encoding.ofId?, Encoding.id, valid]
  | lengthByteArray =>
    by_cases six : id = 6
    · simp [Encoding.ofId?, Encoding.id, six]
    · by_cases seven : id = 7 <;> simp [Encoding.ofId?, Encoding.id, six, seven]
  | byteArray =>
    by_cases six : id = 6
    · simp [Encoding.ofId?, Encoding.id, six]
    · by_cases seven : id = 7 <;> simp [Encoding.ofId?, Encoding.id, six, seven]

private theorem mapError_ok_iff {ε δ α : Type} {action : Except ε α} {f : ε → δ} {value : α} :
    action.mapError f = .ok value ↔ action = .ok value := by
  cases action <;> simp [Except.mapError]

private theorem bind_ok_iff {ε α β : Type} {action : Except ε α} {next : α → Except ε β}
    {output : β} :
    (action >>= next) = .ok output ↔
      ∃ input, action = .ok input ∧ next input = .ok output := by
  cases action <;> simp [Bind.bind, Except.bind]

public theorem decode_ok_iff {kind : Kind} {params : ScalarPage.Parameters} {limits : Limits}
    {source : Bytes} {output : List (Option kind.Value)} :
    decode kind params limits source = .ok output ↔
      ∃ (encoding : Encoding kind) (page : ScalarPage.Prepared) (values : List kind.Value),
        params.encoding = encoding.id ∧
        ScalarPage.prepareFor encoding.id params limits.page source = .ok page ∧
        encoding.read limits (page.mask.count true) page.scalars = .ok values ∧
        output.map Option.isSome = page.mask ∧ output.filterMap id = values := by
  constructor
  · intro h
    unfold decode at h
    cases selected : Encoding.ofId? kind params.encoding with
    | none => rw [selected] at h; contradiction
    | some encoding =>
      rw [selected] at h
      obtain ⟨page, prepared, h⟩ := bind_ok_iff.mp h
      obtain ⟨values, read, h⟩ := bind_ok_iff.mp h
      obtain ⟨shape, order⟩ := FlatPage.reconstruct_ok_iff.mp (mapError_ok_iff.mp h)
      exact ⟨encoding, page, values, encoding_ofId_ok_iff.mp selected,
        mapError_ok_iff.mp prepared, read, shape, order⟩
  · rintro ⟨encoding, page, values, raw, prepared, read, shape, order⟩
    have selected := encoding_ofId_ok_iff.mpr raw
    simp only [decode, selected]
    refine bind_ok_iff.mpr ⟨page, mapError_ok_iff.mpr prepared, ?_⟩
    refine bind_ok_iff.mpr ⟨values, read, ?_⟩
    exact mapError_ok_iff.mpr (FlatPage.reconstruct_ok_iff.mpr ⟨shape, order⟩)

public theorem decode_wire_sound {kind : Kind} {params : ScalarPage.Parameters} {limits : Limits}
    {source : Bytes} {output : List (Option kind.Value)}
    (h : decode kind params limits source = .ok output) :
    ∃ (encoding : Encoding kind) (layout : FlatPage.Layout) (page : ScalarPage.Prepared)
        (values : List kind.Value),
      params.encoding = encoding.id ∧
      ScalarPage.validateFor encoding.id params limits.page source = .ok layout ∧
      ScalarPage.PreparedWire params limits.page layout source page ∧
      encoding.read limits (page.mask.count true) page.scalars = .ok values ∧
      output.map Option.isSome = page.mask ∧ output.filterMap id = values := by
  obtain ⟨encoding, page, values, raw, prepared, read, shape, order⟩ := decode_ok_iff.mp h
  obtain ⟨layout, valid, wire⟩ := ScalarPage.prepareFor_sound prepared
  exact ⟨encoding, layout, page, values, raw, valid, wire, read, shape, order⟩

public theorem decode_counts {kind : Kind} {params : ScalarPage.Parameters} {limits : Limits}
    {source : Bytes} {output : List (Option kind.Value)}
    (h : decode kind params limits source = .ok output) :
    output.length = params.numValues ∧
      match params.version with
      | .v1 _ _ => True
      | .v2 nulls _ _ _ _ => (output.filterMap id).length = params.numValues - nulls := by
  obtain ⟨_, page, values, _, prepared, _, shape, order⟩ := decode_ok_iff.mp h
  obtain ⟨length, counts⟩ := ScalarPage.preparedFor_counts prepared
  refine ⟨?_, ?_⟩
  · have slots := congrArg List.length shape
    rwa [List.length_map, length] at slots
  · have reconstruct := FlatPage.reconstruct_ok_iff.mpr ⟨shape, order⟩
    have present := (FlatPage.reconstruct_exists_iff page.mask values).mp ⟨output, reconstruct⟩
    cases version : params.version with
    | v1 => trivial
    | v2 =>
      rw [version] at counts
      rw [order, ← present]
      exact counts

end Silmaril.Proofs.Formats.Parquet.DeltaPage
