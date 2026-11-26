module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Int96.Mixed.Thms
import Silmaril.Formats.Parquet.Footer.Defs
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Int96.Mixed.Defs
meta import Silmaril.Formats.Parquet.Footer.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril.Formats
open Silmaril.Formats.Parquet.Int96 Silmaril.Formats.Parquet.Int96.Mixed
open Silmaril.Numeric.Timestamp

private def v1 : Bytes := ⟨include_bytes "../../../../../data/parquet-int96-mixed/fallback-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../../data/parquet-int96-mixed/fallback-v2.parquet"⟩
private def v1Word : Bytes := ⟨include_bytes "../../../../../data/parquet-int96-mixed/v1-bad-plain-word.parquet"⟩
private def v2Reference : Bytes := ⟨include_bytes "../../../../../data/parquet-int96-mixed/v2-bad-reference.parquet"⟩

private def withChunk {α : Type} (file : Bytes)
    (callback : Nat → Nat → Parquet.Footer.SchemaElement → Parquet.Footer.ColumnMetadata → α) :
    Option α := do
  let (footer, metadata) ← (Parquet.Footer.readFooter {} file).toOption
  let leaf ← metadata.schema[1]?
  let group ← metadata.rowGroups[0]?
  let column ← group.columns[0]?
  return callback footer.start group.numRows.toNat leaf column.metadata

private def nanos {policy : Policy} (slots : Dictionary.Slots policy) : List (Option Int) :=
  slots.map (Option.map Ticks.ticks)

private def observe (limits : Dictionary.Limits) (policy : Policy) (file : Bytes) :
    Option (Except Error (List (Option Int))) :=
  withChunk file fun footer rows leaf column =>
    (Mixed.read limits policy file footer rows leaf column).map nanos

private def dictA : List (Option Int) := [some (-1), none, some 17, some (-1)]
private def dictB : List (Option Int) := [some 3, none, some 17, some 19]
private def plainA : List (Option Int) :=
  [some 101, none, some (-102), some 103, some 104, none, some (-105), some 106]
private def plainB : List (Option Int) :=
  [some 107, none, some 108, some 109, some 110, some 111, none, some 113]
private def allSlots : List (Option Int) := dictA ++ dictB ++ plainA ++ plainB

#guard observe {} .prolepticUtc v1 = some (.ok allSlots)
#guard observe {} .prolepticLocal v1 = some (.ok allSlots)
#guard observe {} .prolepticUtc v2 = some (.ok allSlots)
#guard observe {} .prolepticLocal v2 = some (.ok allSlots)

-- The leading dictionary is frame 0. The bad present word and reference
-- indexes each count the null before them.
#guard observe {} .prolepticLocal v1Word =
  some (.error ⟨4, .page 3 123 (.plain (.invalidWord 2))⟩)
#guard observe {} .prolepticUtc v2Reference =
  some (.error ⟨4, .page 2 83 (.dictionary (.reference 3 3))⟩)

#guard v2.data[141]! == 0
private def legacyTag : Bytes := ⟨v2.data.set! 141 4⟩
#guard observe {} .prolepticLocal legacyTag = some (.error ⟨4, .page 3 125 (.encoding 2)⟩)

private def withColumn (file : Bytes) (modify : Parquet.Footer.ColumnMetadata → Parquet.Footer.ColumnMetadata)
    (rowCount : Option Nat := none) : Option (Except Error (List (Option Int))) :=
  withChunk file fun footer rows leaf column =>
    (Mixed.read {} .prolepticLocal file footer (rowCount.getD rows) leaf (modify column)).map nanos

#guard withColumn v2 (fun column => { column with dictionaryPageOffset := none }) =
  some (.error ⟨66, .locate .missingDictionary⟩)
#guard withColumn v2 (fun column => { column with dataPageOffset := 67 }) =
  some (.error ⟨4, .page 1 66 .dataOffset⟩)
#guard withColumn v1Word (fun column => { column with numValues := 23 }) (some 23) =
  some (.error ⟨4, .slotCount 23 24⟩)
#guard withColumn v2 (fun column =>
  { column with totalCompressedSize := 320, totalUncompressedSize := 320 }) =
  some (.error ⟨4, .framing .payloadBounds⟩)

private def segment (start stop : Nat) : List UInt8 := (v2.toList.drop start).take (stop - start)
private def leading : List UInt8 := segment 4 66

private def rebuilt (frames : List UInt8) (dataOffset : Int) :
    Option (Except Error (List (Option Int))) :=
  withChunk v2 fun _ rows leaf column =>
    let wire := Bytes.ofList (segment 0 4 ++ frames)
    let changed : Parquet.Footer.ColumnMetadata := { column with
      dataPageOffset := dataOffset, totalCompressedSize := frames.length, totalUncompressedSize := frames.length }
    (Mixed.read {} .prolepticLocal wire wire.length rows leaf changed).map nanos

#guard rebuilt (segment 66 325) 4 =
  some (.error ⟨4, .page 0 4 (.dictionary .expectedDictionary)⟩)
#guard rebuilt leading 66 = some (.error ⟨4, .missingData⟩)
#guard rebuilt (segment 4 325 ++ leading) 66 =
  some (.error ⟨4, .page 5 325 .misplacedDictionary⟩)

-- Alternating the original frames keeps the dispatch local to each header.
#guard rebuilt (leading ++ segment 125 225 ++ segment 66 95 ++ segment 225 325 ++ segment 95 125) 66 =
  some (.ok (plainA ++ dictA ++ plainB ++ dictB))

private def defaults : Dictionary.Limits := {}

#guard observe { defaults with maxEntries := 3 } .prolepticLocal v2 =
  some (.error ⟨4, .page 0 4 (.dictionary .entryLimit)⟩)
#guard observe { defaults with framing.maxPages := 4 } .prolepticLocal v2 =
  some (.error ⟨4, .framing .pageLimit⟩)

-- The standalone readers still reject the opposite data encoding.
#guard (withChunk v2 fun footer rows leaf column =>
    (Dictionary.read {} .prolepticLocal v2 footer rows leaf column).map nanos) =
  some (.error ⟨4, .page 3 125 (.dataEncoding 0)⟩)

private def readDictionaryDataAsPlain : Option (Except Parquet.Int96.Page.Error (List (Option Int))) :=
  withChunk v2 fun _ _ leaf _ =>
    match Parquet.Page.readPage {} v2 ⟨4, 325⟩ 66 with
    | .error _ => .error .unsupportedPage
    | .ok frame => (Parquet.Int96.Page.decode .prolepticLocal leaf 0 frame.value defaults.scalar
        (Dictionary.frameBody v2 frame)).map nanos

#guard readDictionaryDataAsPlain = some (.error (.scalar (.unsupportedEncoding 8)))
