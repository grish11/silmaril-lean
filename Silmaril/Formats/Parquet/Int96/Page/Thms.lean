module

public import Silmaril.Formats.Parquet.Int96.Page.Defs
import Silmaril.Proofs.Formats.Parquet.Int96.Page.Correctness

public section

namespace Silmaril.Formats.Parquet.Int96.Page

/-- The flat leaf and header supply the exact parameters. Only codec zero and
checksum-free pages are admitted. -/
theorem parameters_sound {leaf : Footer.SchemaElement} {codec : Int} {header : Parquet.Page.Header}
    {params : ScalarPage.Parameters} (checked : parameters leaf codec header = .ok params) :
    leafLevels? leaf = some params.schema ∧ codec = 0 ∧ params.codec = codec ∧ header.crc = none ∧
      params.sizes = ⟨header.compressedSize, header.uncompressedSize⟩ ∧
      match header.kind with
      | .dataV1 info => params.numValues = info.numValues ∧ params.encoding = info.encoding ∧
          params.version = .v1 info.definitionLevelEncoding info.repetitionLevelEncoding
      | .dataV2 info => params.numValues = info.numValues ∧ params.encoding = info.encoding ∧
          params.version = .v2 info.numNulls info.numRows info.repetitionBytes info.definitionBytes
            (some info.isCompressed)
      | _ => False :=
  Proofs.Formats.Parquet.Int96.Page.parameters_sound checked

/-- The ordered logical slots reproduce each original word exactly. Nulls
occupy the same positions. -/
theorem decodeSlots_eq_ok_iff (start : Nat) (raw : List (Option Bytes))
    (payloads : List (Option Payload)) :
    decodeSlots start raw = .ok payloads ↔
      raw.map (Option.map Bytes.toList) = payloads.map (Option.map Payload.encode) :=
  Proofs.Formats.Parquet.Int96.Page.decodeSlots_eq_ok_iff start raw payloads

/-- The reported index is the first invalid present word's logical slot,
counting nulls in the successful prefix. -/
theorem decodeSlots_eq_invalidWord_iff (start : Nat) (raw : List (Option Bytes)) (index : Nat) :
    decodeSlots start raw = .error (.invalidWord index) ↔
      ∃ before bad after, raw = before ++ some bad :: after ∧
        (∃ payloads, decodeSlots start before = .ok payloads) ∧
        Payload.decode? bad.toList = none ∧ index = start + before.length :=
  Proofs.Formats.Parquet.Int96.Page.decodeSlots_eq_invalidWord_iff start raw index

/-- Successful decoding is exactly the policy's pointwise interpretation of the
original nullable words. -/
theorem decode_eq_ok_iff {policy : Policy} {leaf : Footer.SchemaElement} {codec : Int}
    {header : Parquet.Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {output : List (Option (Value policy))} :
    decode policy leaf codec header limits body = .ok output ↔
      ∃ params raw, ∃ payloads : List (Option Payload), parameters leaf codec header = .ok params ∧
        ScalarPage.decode (.fixedLenBytes 12) params limits body = .ok raw ∧
        raw.map (Option.map Bytes.toList) = payloads.map (Option.map Payload.encode) ∧
        output = payloads.map (Option.map (·.toTicks policy)) :=
  Proofs.Formats.Parquet.Int96.Page.decode_eq_ok_iff

/-- An indexed word failure identifies the bad word in the successfully framed
logical slots. -/
theorem decode_eq_invalidWord_iff {policy : Policy} {leaf : Footer.SchemaElement} {codec : Int}
    {header : Parquet.Page.Header} {limits : ScalarPage.Limits} {body : Bytes} {index : Nat} :
    decode policy leaf codec header limits body = .error (.invalidWord index) ↔
      ∃ params before bad after, parameters leaf codec header = .ok params ∧
        ScalarPage.decode (.fixedLenBytes 12) params limits body = .ok (before ++ some bad :: after) ∧
        (∃ payloads, decodeSlots 0 before = .ok payloads) ∧
        Payload.decode? bad.toList = none ∧ index = before.length :=
  Proofs.Formats.Parquet.Int96.Page.decode_eq_invalidWord_iff

/-- Both declared page sizes match the original body. Decoded payloads
re-encode the entire PLAIN suffix in mask order. -/
theorem decode_wire_sound {policy : Policy} {leaf : Footer.SchemaElement} {codec : Int}
    {header : Parquet.Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {output : List (Option (Value policy))}
    (decoded : decode policy leaf codec header limits body = .ok output) :
    body.length = header.compressedSize ∧ body.length = header.uncompressedSize ∧
      ∃ params layout prepared, ∃ payloads : List (Option Payload),
        parameters leaf codec header = .ok params ∧
        ScalarPage.validate params limits body = .ok layout ∧
        ScalarPage.PreparedWire params limits layout body prepared ∧
        output.map Option.isSome = prepared.mask ∧
        prepared.scalars.toList = (payloads.filterMap id).flatMap Payload.encode ∧
        prepared.scalars.length = prepared.mask.count true * 12 ∧
        output = payloads.map (Option.map (·.toTicks policy)) :=
  Proofs.Formats.Parquet.Int96.Page.decode_wire_sound decoded

/-- Both versions preserve the declared slot count. V2 also preserves the
declared present count. -/
theorem decode_counts {policy : Policy} {leaf : Footer.SchemaElement} {codec : Int}
    {header : Parquet.Page.Header} {limits : ScalarPage.Limits} {body : Bytes}
    {output : List (Option (Value policy))}
    (decoded : decode policy leaf codec header limits body = .ok output) :
    match header.kind with
    | .dataV1 info => output.length = info.numValues
    | .dataV2 info => output.length = info.numValues ∧
        (output.filterMap id).length = info.numValues - info.numNulls
    | _ => False :=
  Proofs.Formats.Parquet.Int96.Page.decode_counts decoded

end Silmaril.Formats.Parquet.Int96.Page
