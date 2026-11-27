module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
import Silmaril.Formats.Hive.Manifest.Inventory.Thms
import Silmaril.Formats.Hive.PartitionPath.Positional.Render.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs

namespace Silmaril.Formats.Hive.Manifest.RenderedPositional

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Relational
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)
open PartitionPath (Partition)
open PartitionPath.Positional (RenderLimits)

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩
private def physical := Int32ByteArrayGroup.File.schema ordinal payload
private def partitions : PartitionSchema Kind :=
  ⟨#[⟨"year", .int32 .optional, .reject⟩, ⟨"region", .byteArray .optional, .reject⟩]⟩
private def admission : Inventory.Limits := ⟨8, 160⟩
private def renderLimits : RenderLimits := ⟨128, 64⟩
private def keys := ["region", "year"]
private def region := "café/blue=%5F:west\\x"
private def canonical := "caf%C3%A9%2Fblue%3D%255F%3Awest%5Cx/7/part.parquet"
private def lowerEscape := "caf%C3%A9%2fblue%3D%255F%3Awest%5Cx/7/B%2Eparquet"
private def zebra := "zebra/7/z.parquet"
private def pruned := "apart/8/skip.parquet"
private def late := "zz-later/7/late.parquet"
private def controls := "folder/_common_metadata"

private def entries (region year : String) : Partition :=
  [("region", some region), ("year", some year)]

private def path (region year leaf : String) :=
  (PartitionPath.Positional.render renderLimits keys .uri {} (entries region year)).map
    (fun directory => directory ++ "/" ++ leaf)

private def listing : Except PartitionPath.Positional.RenderError (List String) := do
  let first ← path region "7" "part.parquet"
  let last ← path "zebra" "7" "z.parquet"
  let skip ← path "apart" "8" "skip.parquet"
  return [last, first, controls, skip, lowerEscape, first]

private def fixture : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩

private def lookup (path : String) : Except String Bytes :=
  if path == canonical || path == lowerEscape || path == zebra then .ok fixture
  else if path == late then .ok ⟨fixture.data.set! 122 6⟩
  else .error "literal snapshot missing"

private def keep : Scan.Predicate partitions.toScan Value :=
  fun row => (row ⟨0, by decide⟩).map (· == (7 : Int32))
private def projection : Scan.Projection (partitions.extend physical) :=
  Scan.Projection.ofArray #[⟨3, by decide⟩, ⟨0, by decide⟩, ⟨2, by decide⟩, ⟨3, by decide⟩, ⟨1, by decide⟩]
private def zero : Scan.Projection (partitions.extend physical) := Scan.Projection.ofArray #[]

private abbrev RuntimeError := FileError (Int32ByteArray.Error String)
private abbrev ProjectedRow := Option Bytes × Option Int32 × Option Int32 × Option Bytes × Option Bytes

private def expectedRows (value : String) : List ProjectedRow :=
  let text : Option Bytes := some ⟨value.toUTF8⟩
  let ordinals : List Int32 := [-2147483648, 0, 17, 2147483647, -1]
  let payloads := [none, some Bytes.empty, some (Bytes.ofList [0xFF, 0]),
    some (Bytes.ofList [0x80]), some (Bytes.ofList [120, 121])]
  ordinals.zipWith (fun id bytes => (text, some id, some 7, text, bytes)) payloads

private def counts : List Nat := [3, 0, 2, 3, 0, 2, 3, 0, 2, 3, 0, 2]
private def rows := expectedRows region ++ expectedRows region ++ expectedRows region ++ expectedRows "zebra"

private def run (budget : Nat) (paths : List String)
    (maxDirectoryBytes : Nat := renderLimits.maxDirectoryBytes) :=
  scan (int32 := ordinal) (byteArray := payload) admission maxDirectoryBytes keys .uri {}
    Int32ByteArray.Ingress.convert paths {} lookup projection keep budget

private def observes (budget : Nat) (extra : List String) (expectedCounts : List Nat)
    (expected : List ProjectedRow) (termination : Events.Termination RuntimeError) : Bool := Id.run do
  let .ok paths := listing | return false
  let .ok trace := run budget (paths ++ extra) | return false
  return trace.batches.map (·.rowCount) == expectedCounts &&
    trace.rows.map (fun row =>
      ((row ⟨0, by decide⟩ : Option Bytes), (row ⟨1, by decide⟩ : Option Int32),
        (row ⟨2, by decide⟩ : Option Int32), (row ⟨3, by decide⟩ : Option Bytes),
        (row ⟨4, by decide⟩ : Option Bytes))) == expected &&
    decide (trace.termination = termination)

private def lateFailure : Events.Termination RuntimeError :=
  .readError (.source late (.parquet (.groupFailure 2 (.byteArray (.page 2 1 "payload" 0 108 (.encoding 3))))))

#guard listing.toOption == some [zebra, canonical, controls, pruned, lowerEscape, canonical]
#guard (path "zz-later" "7" "late.parquet").toOption == some late
#guard observes 19 [] counts rows .closed
#guard observes 20 [] counts rows .eos
#guard fixture.data[122]! == 0
#guard observes 23 [late] (counts ++ [3, 0]) (rows ++ (expectedRows "zz-later").take 3) .closed
#guard observes 24 [late] (counts ++ [3, 0]) (rows ++ (expectedRows "zz-later").take 3) lateFailure

#guard match listing with
  | .error _ => false
  | .ok paths =>
    match scan (int32 := ordinal) (byteArray := payload) admission renderLimits.maxDirectoryBytes keys .uri {}
        Int32ByteArray.Ingress.convert paths {} lookup zero keep 20 with
    | .error _ => false
    | .ok trace => trace.batches.map (·.rowCount) == counts && trace.rows.length == 20 &&
        decide (trace.termination = .eos)

#guard match listing with
  | .error _ => false
  | .ok paths =>
    match prepareOrderedInventoryWith physical partitions admission
        (PartitionPath.Positional.parse renderLimits.maxDirectoryBytes keys .uri) {}
        Int32ByteArray.Ingress.convert paths with
    | .error _ => false
    | .ok files =>
      let trace := scanInt32ByteArraySnapshotsBounded {} lookup projection keep 20 files
      files.map (·.path.declared) == [pruned, canonical, canonical, lowerEscape, zebra] &&
        trace.batches.isEmpty &&
        decide (trace.termination = .readError (.open pruned (.lookup "literal snapshot missing")))

#guard match run 0 [controls, pruned] 6 with
  | .ok _ => false
  | .error reason => reason == .entry 1 (.partitionPath pruned (.directoryByteLimit 6 7))

#guard
  let bad := "apart/not-int/skip.parquet"
  match run 0 [controls, bad] with
  | .ok _ => false
  | .error reason => reason == .entry 1 (.binding bad (.conversion "year" (.invalidInt32 "not-int")))

#guard
  let marker := "__HIVE_DEFAULT_PARTITION__/7/part.parquet"
  match run 0 [marker] with
  | .ok _ => false
  | .error reason => reason == .entry 0 (.partitionPath marker (.nullMarkerCollision "region"))

#print axioms scan_eq_reference
#print axioms PartitionPath.Positional.parse_of_rendered_spelling
#print axioms prepareInventoryReferenceWithFileParser_congr

end Silmaril.Formats.Hive.Manifest.RenderedPositional
