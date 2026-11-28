module

public import Silmaril.Formats.Parquet.Timestamp.Page.Defs
import Silmaril.Proofs.Formats.Parquet.Timestamp.Page.Decode

/-! # Header, null-mask, and signed-value preservation -/

public section

namespace Silmaril.Formats.Parquet.Timestamp.Page

open Numeric.Timestamp

/-- Successful parameter selection uses the matched schema levels and every
    relevant field of the caller's data-page header. -/
theorem parameters_sound {leaf : Footer.SchemaElement} {levels : FlatPage.LevelSchema}
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
      | _ => False :=
  Proofs.Formats.Parquet.Timestamp.Page.parameters_sound checked

/-- Logical decoding is exactly the ordered pointwise interpretation of the
    accepted physical slots. -/
theorem decode_eq_ok_iff {binding : Binding} {levels : FlatPage.LevelSchema} {codec : Int}
    {header : Parquet.Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {output : List (Option (Value binding))} :
    decode binding levels codec header limits body = .ok output ↔
      ∃ params raw,
        parameters binding.leaf levels codec header = .ok params ∧
        ScalarPage.decode .int64 params limits body = .ok raw ∧
        output = raw.map (Option.map binding.descriptor.decode) :=
  Proofs.Formats.Parquet.Timestamp.Page.decode_eq_ok_iff

/-- Successful output has the checked definition mask and contains the exact
    signed counts from the PLAIN stream in wire order. -/
theorem decode_sound {binding : Binding} {levels : FlatPage.LevelSchema} {codec : Int}
    {header : Parquet.Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {output : List (Option (Value binding))}
    (decoded : decode binding levels codec header limits body = .ok output) :
    body.length = header.compressedSize ∧
      ∃ params prepared words,
        parameters binding.leaf levels codec header = .ok params ∧
        ScalarPage.prepare params limits body = .ok prepared ∧
        Plain.decodeInt64 (prepared.mask.count true) prepared.scalars = .ok words ∧
        output.map Option.isSome = prepared.mask ∧
        output.filterMap id = words.map binding.descriptor.decode ∧
        (output.filterMap id).map Ticks.ticks = words.map Int64.toInt :=
  Proofs.Formats.Parquet.Timestamp.Page.decode_sound decoded

/-- The slot count matches either header version. V2 also declares the
    number of present values through its null count. -/
theorem decode_counts {binding : Binding} {levels : FlatPage.LevelSchema} {codec : Int}
    {header : Parquet.Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {output : List (Option (Value binding))}
    (decoded : decode binding levels codec header limits body = .ok output) :
    match header.kind with
    | .dataV1 info => output.length = info.numValues
    | .dataV2 info => output.length = info.numValues ∧
        (output.filterMap id).length = info.numValues - info.numNulls
    | _ => False :=
  Proofs.Formats.Parquet.Timestamp.Page.decode_counts decoded

end Silmaril.Formats.Parquet.Timestamp.Page
