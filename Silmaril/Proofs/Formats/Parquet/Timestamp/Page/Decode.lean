module

public import Silmaril.Formats.Parquet.Timestamp.Page.Defs
import Silmaril.Formats.Parquet.ScalarPage.Thms

namespace Silmaril.Proofs.Formats.Parquet.Timestamp.Page

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Formats.Parquet.Timestamp
open Silmaril.Formats.Parquet.Timestamp.Page (Value leafLevels? parameters)
open Silmaril.Numeric.Timestamp

public theorem parameters_sound {leaf : Footer.SchemaElement} {levels : FlatPage.LevelSchema}
    {codec : Int} {header : Parquet.Page.Header} {params : ScalarPage.Parameters}
    (checked : parameters leaf levels codec header = .ok params) :
    leafLevels? leaf = some levels ∧ params.schema = levels ∧ params.codec = codec ∧
      params.sizes = ⟨header.compressedSize, header.uncompressedSize⟩ ∧
      match header.kind with
      | .dataV1 info => params.numValues = info.numValues ∧ params.encoding = info.encoding ∧
          params.version = .v1 info.definitionLevelEncoding info.repetitionLevelEncoding
      | .dataV2 info => params.numValues = info.numValues ∧ params.encoding = info.encoding ∧
          params.version = .v2 info.numNulls info.numRows info.repetitionBytes info.definitionBytes
            (some info.isCompressed)
      | _ => False := by
  unfold parameters at checked
  split at checked
  · rename_i layout
    cases kind : header.kind <;> simp only [kind, Except.ok.injEq] at checked
    · subst params
      exact ⟨layout, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · contradiction
    · subst params
      exact ⟨layout, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · contradiction
  · contradiction

public theorem decode_eq_ok_iff {binding : Binding} {levels : FlatPage.LevelSchema} {codec : Int}
    {header : Parquet.Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {output : List (Option (Value binding))} :
    Timestamp.Page.decode binding levels codec header limits body = .ok output ↔
      ∃ params raw,
        parameters binding.leaf levels codec header = .ok params ∧
        ScalarPage.decode .int64 params limits body = .ok raw ∧
        output = raw.map (Option.map binding.descriptor.decode) := by
  constructor
  · intro decoded
    cases checked : parameters binding.leaf levels codec header with
    | error error => simp [Timestamp.Page.decode, checked, bind, Except.bind] at decoded
    | ok params =>
      cases physical : ScalarPage.decode .int64 params limits body with
      | error error => simp [Timestamp.Page.decode, checked, physical, Except.mapError, bind, Except.bind] at decoded
      | ok raw =>
        refine ⟨params, raw, rfl, physical, ?_⟩
        simpa [Timestamp.Page.decode, checked, physical, Except.mapError, bind, Except.bind,
          pure, Except.pure] using decoded.symm
  · rintro ⟨params, raw, checked, physical, rfl⟩
    simp [Timestamp.Page.decode, checked, physical, Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem present_map {α β : Type} (slots : List (Option α)) (f : α → β) :
    (slots.map (Option.map f)).filterMap id = (slots.filterMap id).map f := by
  induction slots with
  | nil => rfl
  | cons value rest ih => cases value <;> simp [ih]

private theorem bodySize {params : ScalarPage.Parameters} {limits : ScalarPage.Limits} {body : Bytes}
    {layout : FlatPage.Layout} (checked : ScalarPage.validate params limits body = .ok layout) :
    body.length = params.sizes.compressed := by
  by_contra mismatch
  simp only [ScalarPage.validate, ScalarPage.validateFor] at checked
  split at checked
  · contradiction
  split at checked
  · contradiction
  split at checked
  · contradiction
  split at checked
  · contradiction
  simp at checked

public theorem decode_sound {binding : Binding} {levels : FlatPage.LevelSchema} {codec : Int}
    {header : Parquet.Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {output : List (Option (Value binding))}
    (decoded : Timestamp.Page.decode binding levels codec header limits body = .ok output) :
    body.length = header.compressedSize ∧
      ∃ params prepared words,
        parameters binding.leaf levels codec header = .ok params ∧
        ScalarPage.prepare params limits body = .ok prepared ∧
        Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
        output.map Option.isSome = prepared.mask ∧
        output.filterMap id = words.map binding.descriptor.decode ∧
        (output.filterMap id).map Ticks.ticks = words.map Int64.toInt := by
  obtain ⟨params, raw, checked, physical, rfl⟩ := decode_eq_ok_iff.mp decoded
  obtain ⟨prepared, words, prepare, read, mask, ordered, _, _⟩ := ScalarPage.decode_sound physical
  obtain ⟨_, validated, _⟩ := ScalarPage.prepare_sound prepare
  have extent := bodySize validated
  rw [(parameters_sound checked).2.2.2.1] at extent
  have present := (present_map raw binding.descriptor.decode).trans (congrArg (List.map _) ordered)
  refine ⟨extent, params, prepared, words, checked, prepare, read, ?_, present, ?_⟩
  · simpa [List.map_map, Function.comp_def] using mask
  · rw [present, List.map_map]
    rfl

public theorem decode_counts {binding : Binding} {levels : FlatPage.LevelSchema} {codec : Int}
    {header : Parquet.Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {output : List (Option (Value binding))}
    (decoded : Timestamp.Page.decode binding levels codec header limits body = .ok output) :
    match header.kind with
    | .dataV1 info => output.length = info.numValues
    | .dataV2 info => output.length = info.numValues ∧
        (output.filterMap id).length = info.numValues - info.numNulls
    | _ => False := by
  obtain ⟨params, raw, checked, physical, rfl⟩ := decode_eq_ok_iff.mp decoded
  have fields := (parameters_sound checked).2.2.2.2
  obtain ⟨slots, present⟩ := ScalarPage.decode_counts physical
  cases headerKind : header.kind <;> simp only [headerKind] at fields ⊢
  · simp [slots, fields.1]
  · rw [fields.2.2] at present
    refine ⟨by simpa only [List.length_map, fields.1] using slots, ?_⟩
    rw [present_map, List.length_map]
    simpa only [fields.1] using present

end Silmaril.Proofs.Formats.Parquet.Timestamp.Page
