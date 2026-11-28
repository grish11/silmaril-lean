module

import Silmaril.Formats.Parquet.Int96.Page.Thms
meta import Silmaril.Formats.Parquet.Int96.Page.Defs
meta import Silmaril.Formats.Parquet.Page.Header.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril.Formats Silmaril.Formats.Parquet.Int96 Silmaril.Formats.Parquet.Int96.Page
open Silmaril.Numeric.Timestamp

private def leaf (repetition : Parquet.Footer.Repetition) : Parquet.Footer.SchemaElement :=
  ⟨some .int96, none, some repetition, "legacy_ts", none⟩

private def limits : Parquet.ScalarPage.Limits := ⟨128, 128, ⟨16, 64⟩, 0⟩

private def withPage {α : Type} (bytes : List UInt8) (read : Parquet.Page.Header → Bytes → α) :
    Option α :=
  match Parquet.Page.readHeaderPrefix {} (.ofList bytes) with
  | .error _ => none
  | .ok (header, consumed) => some (read header (.ofList (bytes.drop consumed)))

private def ticks (policy : Policy) (header : Parquet.Page.Header) (body : Bytes) :
    Except Error (List (Option Int)) :=
  (decode policy (leaf .optional) 0 header limits body).map (List.map (Option.map Ticks.ticks))

-- BEGIN pinned PyArrow frames
private def v1Group0 : List UInt8 :=
  [21, 0, 21, 84, 21, 84, 44, 21, 8, 21, 0, 21, 6, 21, 6, 28, 0, 0, 0, 2, 0, 0, 0, 3, 11, 0, 0,
   0, 175, 177, 0, 0, 0, 140, 156, 35, 0, 255, 255, 78, 145, 148, 78, 0, 0, 138, 61, 37, 0, 255,
   255, 78, 145, 148, 78, 0, 0, 139, 61, 37, 0]
private def v1Group1 : List UInt8 :=
  [21, 0, 21, 84, 21, 84, 44, 21, 6, 21, 0, 21, 6, 21, 6, 28, 0, 0, 0, 2, 0, 0, 0, 6, 1, 0, 0,
   0, 0, 0, 0, 0, 0, 140, 61, 37, 0, 1, 0, 0, 0, 0, 0, 0, 0, 140, 61, 37, 0, 255, 255, 78, 226,
   226, 77, 0, 0, 139, 222, 38, 0]
private def v2Group0 : List UInt8 :=
  [21, 6, 21, 76, 21, 76, 92, 21, 8, 21, 2, 21, 8, 21, 0, 21, 4, 21, 0, 18, 28, 0, 0, 0, 3, 13,
   232, 3, 0, 0, 0, 0, 0, 0, 55, 159, 34, 0, 216, 185, 63, 145, 148, 78, 0, 0, 139, 61, 37, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 140, 61, 37, 0]
private def v2Group1 : List UInt8 :=
  [21, 6, 21, 52, 21, 52, 92, 21, 6, 21, 2, 21, 6, 21, 0, 21, 4, 21, 0, 18, 28, 0, 0, 0, 3, 6,
   232, 3, 0, 0, 0, 0, 0, 0, 140, 61, 37, 0, 0, 0, 68, 41, 53, 58, 0, 0, 168, 1, 39, 0]
private def v2BadGroup1 : List UInt8 :=
  [21, 6, 21, 52, 21, 52, 92, 21, 6, 21, 2, 21, 6, 21, 0, 21, 4, 21, 0, 18, 28, 0, 0, 0, 3, 6,
   232, 3, 0, 0, 0, 0, 0, 0, 140, 61, 37, 0, 0, 0, 79, 145, 148, 78, 0, 0, 168, 1, 39, 0]
-- END pinned PyArrow frames

#guard withPage v1Group0 (ticks .prolepticUtc) =
  some (.ok [some (-9223372036854775808), some (-86400000000001), none, some (-1)])
#guard withPage v1Group1 (ticks .prolepticLocal) =
  some (.ok [some 0, some 1, some 9223372036854775807])
#guard withPage v2Group0 (ticks .prolepticLocal) =
  some (.ok [some (-14826671999999999000), none, some (-1001000), some 0])
#guard withPage v2Group1 (ticks .prolepticUtc) =
  some (.ok [none, some 1000, some 10000000000000000000])
#guard withPage v2Group1 (ticks .prolepticLocal) =
  some (.ok [none, some 1000, some 10000000000000000000])
#guard withPage v2BadGroup1 (ticks .prolepticUtc) = some (.error (.invalidWord 2))
#guard withPage v2BadGroup1 (ticks .prolepticLocal) = some (.error (.invalidWord 2))

-- An admitted nanosecond coordinate can narrow exactly to one unit and fail at another.
private def narrowed (unit : TickUnit) (header : Parquet.Page.Header) (body : Bytes) :
    Except Error (List (Option (Except ConversionError Int64))) :=
  (decode .prolepticLocal (leaf .optional) 0 header limits body).map
    (List.map fun slot => slot.map (·.toInt64 unit))

#guard withPage v2Group1 (narrowed .nanosecond) =
  some (.ok [none, some (.ok 1000), some (.error .outOfRange)])
#guard withPage v2Group1 (narrowed .microsecond) =
  some (.ok [none, some (.ok 1), some (.ok 10000000000000000)])
#guard withPage v2Group1 (narrowed .millisecond) =
  some (.ok [none, some (.error .precisionLoss), some (.ok 10000000000000)])

-- The wire admits all signed Julian days, even beyond the producer's timestamp types.
private def signedDayEndpoints : Bytes := .ofList
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 128, 255, 255, 78, 145, 148, 78, 0, 0, 255, 255, 255, 127]

private def requiredV1 : Parquet.Page.Header := ⟨24, 24, none, .dataV1 ⟨2, 0, 3, 3⟩⟩

#guard (decode .prolepticUtc (leaf .required) 0 requiredV1 limits signedDayEndpoints).map
  (List.map (Option.map Ticks.ticks)) =
  .ok [some (-185753453990400000000000), some 185331720383999999999999]

#guard decode .prolepticUtc (leaf .repeated) 0 requiredV1 limits signedDayEndpoints
  matches .error .schemaLevels
#guard decode .prolepticUtc { leaf .required with physicalType := some .fixedLenByteArray }
    0 requiredV1 limits signedDayEndpoints
  matches .error .schemaLevels
#guard decode .prolepticUtc (leaf .required) 1 requiredV1 limits signedDayEndpoints
  matches .error (.unsupportedCodec 1)
#guard decode .prolepticUtc (leaf .required) 0 { requiredV1 with crc := some 0 }
    limits signedDayEndpoints
  matches .error .unsupportedChecksum
#guard decode .prolepticUtc (leaf .required) 0 { requiredV1 with kind := .dictionary ⟨2, 0, none⟩ }
    limits signedDayEndpoints
  matches .error .unsupportedPage
#guard decode .prolepticUtc (leaf .required) 0 { requiredV1 with kind := .dataV1 ⟨2, 8, 3, 3⟩ }
    limits signedDayEndpoints
  matches .error (.scalar (.unsupportedEncoding 8))
#guard decode .prolepticUtc (leaf .required) 0 { requiredV1 with kind := .dataV1 ⟨2, 0, 4, 3⟩ }
    limits signedDayEndpoints
  matches .error (.scalar .unsupportedLevelEncoding)
#guard decode .prolepticUtc (leaf .required) 0 requiredV1 limits (.ofList (signedDayEndpoints.toList.take 23))
  matches .error (.scalar (.payload .compressedSizeMismatch))
#guard decode .prolepticUtc (leaf .required) 0 { requiredV1 with uncompressedSize := 25, compressedSize := 25 }
    limits (signedDayEndpoints.push 0)
  matches .error (.scalar (.plain .trailingBytes))
#guard decode .prolepticUtc (leaf .required) 0 requiredV1 { limits with compressedBytes := 23 }
    signedDayEndpoints
  matches .error (.scalar (.payload .compressedLimit))
#guard decode .prolepticUtc (leaf .required) 0
    ⟨24, 24, none, .dataV2 ⟨2, 0, 2, 0, 0, 1, false⟩⟩ limits signedDayEndpoints
  matches .error (.scalar (.levels .unexpectedRepetitionSection))
#guard decode .prolepticUtc (leaf .required) 0
    ⟨24, 24, none, .dataV2 ⟨2, 0, 1, 0, 0, 0, false⟩⟩ limits signedDayEndpoints
  matches .error (.scalar .invalidRowCount)
#guard decode .prolepticUtc (leaf .required) 0
    ⟨24, 24, none, .dataV2 ⟨2, 1, 2, 0, 0, 0, false⟩⟩ limits signedDayEndpoints
  matches .error (.scalar (.levels .presentCountMismatch))
