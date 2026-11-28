module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs

namespace Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress

open Silmaril.Formats Silmaril.Formats.Parquet Silmaril.Relational
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩

private def partitions : PartitionSchema Kind :=
  ⟨#[⟨"year", .int32 .optional, .asNull⟩, ⟨"label", .byteArray .optional, .asNull⟩]⟩

private def required : PartitionSchema Kind :=
  ⟨#[⟨"year", .int32 .required, .asNull⟩, ⟨"label", .byteArray .required, .reject⟩]⟩

private def lower := "label=caf%C3%A9%2fblue/year=-2147483648/lower%2Eparquet"
private def upper := "year=2147483647/label=/upper.parquet"
private def missing := "label=__HIVE_DEFAULT_PARTITION__/missing.parquet"
private def marker := "label=%5F_HIVE_DEFAULT_PARTITION__/year=__HIVE_DEFAULT_PARTITION__/null.parquet"
private def overflow := "label=ok/year=2147483648/overflow.parquet"
private def underflow := "year=-2147483649/underflow.parquet"
private def badNumber := "label=ok/year=1.5/bad.parquet"

private def admitted := preparePaths ordinal payload partitions {}

private def fails (spec : PartitionSchema Kind) (paths : List String) (expected : Error) : Bool :=
  match preparePaths ordinal payload spec {} paths with
  | .error error => error == expected
  | .ok _ => false

#guard match admitted [lower, upper, lower, marker, missing] with
  | .ok files => files.map (fun file =>
      (file.path.declared, file.cells ⟨0, by decide⟩, file.cells ⟨1, by decide⟩)) ==
      [(lower, some (-2147483648), some ⟨"café/blue".toUTF8⟩),
       (upper, some 2147483647, some Bytes.empty),
       (lower, some (-2147483648), some ⟨"café/blue".toUTF8⟩),
       (marker, none, none), (missing, none, none)]
  | .error _ => false

#guard match admitted [lower] with
  | .ok [file] => file.path.canonicalDirectory == "label=caf%C3%A9%2Fblue/year=-2147483648" &&
      file.path.filename == "lower%2Eparquet"
  | _ => false

#guard fails partitions [lower, overflow, "bad//path"]
  (.prepare (.binding overflow (.conversion "year" (.int32OutOfRange 2147483648))))
#guard fails partitions [underflow]
  (.prepare (.binding underflow (.conversion "year" (.int32OutOfRange (-2147483649)))))
#guard fails partitions [badNumber]
  (.prepare (.binding badNumber (.conversion "year" (.invalidInt32 "1.5"))))
#guard fails partitions ["year=1_0/bad.parquet"]
  (.prepare (.binding "year=1_0/bad.parquet" (.conversion "year" (.invalidInt32 "1_0"))))
#guard fails required [lower, marker, badNumber] (.requiredNull marker "year")
#guard fails required [missing] (.requiredNull missing "year")
#guard fails required ["year=1/label=__HIVE_DEFAULT_PARTITION__/null.parquet"]
  (.requiredNull "year=1/label=__HIVE_DEFAULT_PARTITION__/null.parquet" "label")
#guard fails required ["year=1/missing.parquet"]
  (.prepare (.binding "year=1/missing.parquet" (.missingKey "label")))
#guard fails required ["null.parquet"]
  (.prepare (.binding "null.parquet" (.missingKey "label")))
#guard fails required ["year=bad/label=%FF/bad.parquet"]
  (.prepare (.partitionPath "year=bad/label=%FF/bad.parquet" .invalidUtf8))
#guard fails partitions ["year=bad/other=value/bad.parquet"]
  (.prepare (.binding "year=bad/other=value/bad.parquet" (.unknownKey "other")))
#guard fails ⟨#[⟨"ordinal", .int32 .optional, .reject⟩]⟩ [] (.prepare (.schema (.physicalCollision "ordinal")))

private def fixture : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩

private def lookup (path : String) : Except Unit Bytes :=
  if path == lower || path == upper || path == marker then .ok fixture else .error ()

#guard match admitted [lower, marker, lower, upper] with
  | .ok files =>
    let projection := Scan.Projection.ofArray
      (source := partitions.extend (Int32ByteArrayGroup.File.schema ordinal payload))
      #[⟨2, by decide⟩, ⟨3, by decide⟩]
    let trace := Manifest.scan (int32ByteArraySnapshotOpener {} ordinal payload partitions lookup)
      projection (fun _ => some true) files
    let lowerCell := (some (-2147483648 : Int32), some (⟨"café/blue".toUTF8⟩ : Bytes))
    let upperCell := (some (2147483647 : Int32), some Bytes.empty)
    let cells (value : Option Int32 × Option Bytes) := [List.replicate 3 value, [], List.replicate 2 value]
    trace.batches.map (·.rowCount) == [3, 0, 2, 3, 0, 2, 3, 0, 2, 3, 0, 2] &&
      trace.batches.map (fun batch => batch.toRows.map (fun row => (row ⟨0, by decide⟩, row ⟨1, by decide⟩))) ==
        cells lowerCell ++ cells (none, none) ++ cells lowerCell ++ cells upperCell &&
      decide (trace.termination = .eos)
  | .error _ => false

#print axioms convert_int32_ok_iff
#print axioms convert_byteArray
#print axioms preparePath_ok_iff
#print axioms preparePaths_ok_iff
#print axioms preparePaths_preserves_paths

end Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress
