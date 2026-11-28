module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Int96.Dictionary.Thms
import Silmaril.Formats.Parquet.Footer.Defs
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Int96.Dictionary.Defs
meta import Silmaril.Formats.Parquet.Footer.Defs
meta import Silmaril.Numeric.Timestamp.Defs

open Silmaril.Formats
open Silmaril.Formats.Parquet.Int96 Silmaril.Formats.Parquet.Int96.Dictionary
open Silmaril.Numeric.Timestamp

private def v1 : Bytes := ⟨include_bytes "../../../../../data/parquet-int96-dictionary/dictionary-v1.parquet"⟩
private def v2 : Bytes := ⟨include_bytes "../../../../../data/parquet-int96-dictionary/dictionary-v2.parquet"⟩

private def withChunk {α : Type} (file : Bytes) (index : Nat)
    (callback : Nat → Nat → Parquet.Footer.SchemaElement → Parquet.Footer.ColumnMetadata → α) :
    Option α := do
  let (footer, metadata) ← (Parquet.Footer.readFooter {} file).toOption
  let leaf ← metadata.schema[1]?
  let group ← metadata.rowGroups[index]?
  let column ← group.columns[0]?
  return callback footer.start group.numRows.toNat leaf column.metadata

private def observe (limits : Limits) (policy : Policy) (file : Bytes) (index : Nat) :
    Option (Except Error (List (Option Int))) :=
  withChunk file index fun footer rows leaf column =>
    (Dictionary.read limits policy file footer rows leaf column).map (List.map (Option.map Ticks.ticks))

#guard observe {} .prolepticUtc v1 0 =
  some (.ok [some (-1001), none, some (-1), some (-1001), some 0, some (-1)])
#guard observe {} .prolepticLocal v1 1 =
  some (.ok [some 3, some (-4), none, some 3, some 5, none])
#guard observe {} .prolepticUtc v2 0 =
  some (.ok [some (-2000), none, some (-1000), some (-2000), some 10000000000000000000, some (-1000)])
#guard observe {} .prolepticLocal v2 1 =
  some (.ok [some 6000, some (-7000), none, some 6000, some 8000, none])

-- In group 1 the third present reference is at logical slot 3, after a null.
#guard v2.data[162]! == 0x84
private def badReference : Bytes := ⟨v2.data.set! 162 0xb4⟩
#guard observe {} .prolepticUtc badReference 1 = some (.error ⟨84, .page 1 134 (.reference 3 3)⟩)

-- Dictionary entry 1 has an invalid subday even though one of the data slots is null.
private def badEntry : Bytes := .ofList
  (v2.toList.take 110 ++ [0, 0, 79, 145, 148, 78, 0, 0] ++ v2.toList.drop 118)
#guard observe {} .prolepticLocal badEntry 1 =
  some (.error ⟨84, .page 0 84 (.dictionaryEntry (.invalidWord 1))⟩)

#guard v2.data[148]! == 16
private def plainFallback : Bytes := ⟨v2.data.set! 148 0⟩
#guard observe {} .prolepticLocal plainFallback 1 =
  some (.error ⟨84, .page 1 134 (.dataEncoding 0)⟩)
#guard v2.data[94]! == 0
private def wrongDictionaryTag : Bytes := ⟨v2.data.set! 94 4⟩
#guard observe {} .prolepticLocal wrongDictionaryTag 1 =
  some (.error ⟨84, .page 0 84 (.dictionaryEncoding 2)⟩)

private def dictionaryFrame : List UInt8 := (v2.toList.drop 84).take 50
private def dataFrame : List UInt8 := (v2.toList.drop 134).take 30

private def rebuilt (frames : List UInt8) (dataOffset : Int) (rows : Nat := 6) :
    Option (Except Error (List (Option Int))) :=
  withChunk v2 1 fun _ _ leaf column =>
    let body : Bytes := .ofList ([80, 65, 82, 49] ++ frames)
    let changed := { column with
      dictionaryPageOffset := some 4
      dataPageOffset := dataOffset
      numValues := rows
      totalCompressedSize := frames.length
      totalUncompressedSize := frames.length }
    (Dictionary.read {} .prolepticLocal body body.length rows leaf changed).map
      (List.map (Option.map Ticks.ticks))

-- Both data versions use the same chunk-local dictionary.
private def v1DataFrame : List UInt8 := (v1.toList.drop 133).take 29
private def localGroup : List (Option Int) := [some 6000, some (-7000), none, some 6000, some 8000, none]
#guard rebuilt (dictionaryFrame ++ v1DataFrame ++ dataFrame) 54 12 =
  some (.ok (localGroup ++ localGroup))

#guard rebuilt (dictionaryFrame ++ dataFrame ++ dictionaryFrame) 54 =
  some (.error ⟨4, .page 2 84 .misplacedDictionary⟩)
#guard rebuilt (dataFrame ++ dictionaryFrame) 4 =
  some (.error ⟨4, .page 0 4 .expectedDictionary⟩)
#guard rebuilt (dictionaryFrame ++ dataFrame) 55 =
  some (.error ⟨4, .page 1 54 .dataOffset⟩)

private def limits : Limits := {}
#guard observe { limits with maxEntries := 2 } .prolepticLocal v2 1 =
  some (.error ⟨84, .page 0 84 .entryLimit⟩)
#guard observe { limits with maxDictionaryBytes := 35 } .prolepticLocal v2 1 =
  some (.error ⟨84, .page 0 84 .dictionaryByteLimit⟩)
#guard observe { limits with framing.maxPages := 1 } .prolepticLocal v2 1 =
  some (.error ⟨84, .framing .pageLimit⟩)
