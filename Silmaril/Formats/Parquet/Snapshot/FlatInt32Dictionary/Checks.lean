module

import Batteries.Data.Except
import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.Thms
import Silmaril.Formats.Parquet.FlatInt32Writer.Defs
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary.Defs
meta import Silmaril.Formats.Parquet.FlatInt32Writer.Defs

/-! Whole-file observations through the checked Snapshot cursor. -/

namespace Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary

open Silmaril.Relational Silmaril.Formats.Arrow

private def mixed : Bytes := ⟨include_bytes "../../../../../data/parquet-dictionary-snapshot/mixed-v2.parquet"⟩
private def crcPlain : Bytes := ⟨include_bytes "../../../../../data/parquet-dictionary-snapshot/crc-plain-v2.parquet"⟩
private def crcDictionary : Bytes := ⟨include_bytes "../../../../../data/parquet-dictionary-snapshot/crc-dictionary-v2.parquet"⟩
private def snappyPlain : Bytes := ⟨include_bytes "../../../../../data/parquet-dictionary-snapshot/snappy-plain-v2.parquet"⟩
private def snappyDictionary : Bytes := ⟨include_bytes "../../../../../data/parquet-dictionary-snapshot/snappy-dictionary-v2.parquet"⟩
private def arrowV1 : Bytes := ⟨include_bytes "../../../../../data/parquet-dictionary-chunk/arrow-v1.parquet"⟩
private def arrowV2 : Bytes := ⟨include_bytes "../../../../../data/parquet-dictionary-chunk/arrow-v2.parquet"⟩
private def javaV1 : Bytes := ⟨include_bytes "../../../../../data/parquet-dictionary-chunk/java-v1.parquet"⟩
private def javaV2 : Bytes := ⟨include_bytes "../../../../../data/parquet-dictionary-chunk/java-v2.parquet"⟩
private def plain : Bytes := ⟨include_bytes "../../../../../tools/parquet-flat-scan/fixtures/flat-plain-v2.parquet"⟩

private def schema : Scan.Schema String Unit :=
  ⟨2, fun i => (if i.val = 0 then "required_i32" else "optional_i32", ())⟩

private abbrev Observation (ε : Type) := List Nat × List (List (Option Int32)) × Events.Termination ε

private def observed {ε : Type} (events : Events.EventStream String FlatInt32.Cell ε) :
    Except ε (Observation ε) :=
  events.map fun ⟨_, trace⟩ => (trace.batches.map (·.rowCount), trace.rows.map List.ofFn, trace.termination)

private def read (limits : Limits) (bytes : Bytes) :
    Except (Snapshot.Error Error) (Observation (Snapshot.Error Error)) :=
  observed (readAll limits schema bytes)

private def mixedRows (n : Nat) : List (List (Option Int32)) := (List.range n).map fun (i : Nat) =>
  [some (Int32.ofInt (100 + Int.ofNat i)),
    if i % 4 = 0 then none else some (Int32.ofInt (40 * Int.ofNat (i / 8) - 9 + 3 * Int.ofNat (i % 3)))]

private def optional (i : Nat) : Option Int32 :=
  if i % 4 = 0 then none else some (Int32.ofInt (-9 + 7 * Int.ofNat (i % 5)))

private def arrowRows : List (List (Option Int32)) := (List.range 48).map fun (i : Nat) =>
  let required : Nat := i / 24 * 100 + if i % 24 < 8 then i % 3 else i % 24
  [some (Int32.ofInt (Int.ofNat required)), if i < 24 then none else optional i]

private def javaRows : List (List (Option Int32)) := (List.range 192).map fun i =>
  [some (Int32.ofInt (17 - 11 * Int.ofNat (i % 3))), optional i]

#guard read {} mixed = .ok ([8, 8], mixedRows 16, .eos)
#guard read {} arrowV1 = .ok ([24, 24], arrowRows, .eos)
#guard read {} arrowV2 = .ok ([24, 24], arrowRows, .eos)
#guard read {} javaV1 = .ok ([192], javaRows, .eos)
#guard read {} javaV2 = .ok ([192], javaRows, .eos)

-- The independent Thrift oracle locates the index width at byte 302 in the
-- second group's optional dictionary page body, after its definition levels.
private def late : Bytes := ⟨mixed.data.set! 302 33⟩
#guard read {} late = .ok ([8], mixedRows 8,
  .readError (.decode 1 (.column 1 "optional_i32" (.dictionary (.dictionaryPage (.hybrid .invalidWidth))))))

-- Checksummed files exercise both branches. Snappy is rejected before dispatch.
#guard read {} crcPlain = .ok ([], [], .readError (.decode 0 (.column 0 "required_i32" (.plain .crcUnsupported))))
#guard read {} crcDictionary =
  .ok ([], [], .readError (.decode 0 (.column 0 "required_i32" (.dictionary .crcUnsupported))))
#guard read {} snappyPlain = .ok ([], [], .readError (.decode 0 (.column 0 "required_i32" (.codec 1))))
#guard read {} snappyDictionary = .ok ([], [], .readError (.decode 0 (.column 0 "required_i32" (.codec 1))))

-- These budgets precede payload work even if a reached page would fail.
#guard read { maxFileBytes := 0 } (Bytes.ofList [0]) = .error (.input .fileByteLimit)
#guard read { maxGroups := 1 } late = .error (.schema .groupLimit)
#guard read { maxFileRows := 15 } late = .error (.schema .fileRowLimit)
#guard read { maxFileCells := 31 } late = .error (.schema .fileCellLimit)
#guard read { plain.groups.maxRows := 7 } late = .ok ([], [], .readError (.decode 0 .groupRowLimit))
#guard read { plain.groups.maxCells := 15 } late = .ok ([], [], .readError (.decode 0 .groupCellLimit))
#guard read { dictionary.maxEntries := 0 } mixed =
  .ok ([], [], .readError (.decode 0 (.column 1 "optional_i32" (.dictionary .entryLimit))))
#guard read { plain.groups.maxPageBytes := 0 } mixed =
  .ok ([], [], .readError (.decode 0 (.column 0 "required_i32" (.plain .pageByteLimit))))
#guard read { maxFileBytes := mixed.length, maxGroups := 2, maxFileRows := 16, maxFileCells := 32 } mixed =
  .ok ([8, 8], mixedRows 16, .eos)

private def reversed : Scan.Schema String Unit :=
  ⟨2, fun i => schema.kind (if i.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩)⟩
#guard observed (readAll {} reversed mixed) =
  .error (.schema (.schemaNames ["optional_i32", "required_i32"] ["required_i32", "optional_i32"]))

-- Association is checked before the deliberately unusable offset in either branch.
private def associationChecks : Bool := Id.run do
  let .ok (_, metadata) := Footer.readFooter {} mixed | return false
  let some column := metadata.rowGroups.head?.bind (fun group => group.columns.head?) | return false
  let field : FlatScan.Field := ⟨"required_i32", .required⟩
  for offset in [none, some (-1)] do
    let c := { column with metadata.dictionaryPageOffset := offset, metadata.dataPageOffset := -1 }
    if (Internal.readColumn {} mixed 0 field 8 { c with metadata.pathInSchema := ["other"] }).map (fun _ => ()) ≠
        .error (.path ["other"]) then return false
    if (Internal.readColumn {} mixed 0 field 8 { c with metadata.physicalType := .int64 }).map (fun _ => ()) ≠
        .error (.physicalType .int64) then return false
  return true

#guard associationChecks

private def plainObserved : Option (List Nat × List (List (Option Int32))) := do
  let (counts, rows, .eos) ← (observed (FlatInt32.readAll {} schema plain)).toOption | none
  pure (counts, rows)

#guard (read {} plain).toOption = plainObserved.map (fun (counts, rows) => (counts, rows, .eos))
#guard (read {} plain).toOption.isSome

private def zeroRows : Option (Observation (Snapshot.Error Error)) := do
  let limits : FlatInt32Writer.Limits := ⟨16, 4096, {}, ⟨{}, 32, ⟨64, 64, ⟨16, 32⟩, 0⟩⟩⟩
  let file ← (FlatInt32Writer.emit limits ⟨0, [⟨"required_i32", .required []⟩,
    ⟨"optional_i32", .optional []⟩]⟩).toOption
  (read {} file.bytes).toOption

#guard zeroRows = some ([0], [], .eos)

end Silmaril.Formats.Parquet.Snapshot.FlatInt32Dictionary
