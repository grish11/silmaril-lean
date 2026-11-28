module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Scan.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Scan.Defs

namespace Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Relational
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

private def partitions : PartitionSchema Kind :=
  ⟨#[⟨"year", .int32 .required, .reject⟩, ⟨"label", .byteArray .optional, .asNull⟩]⟩

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩
private def physical := Int32ByteArrayGroup.File.schema ordinal payload

private def clean : Bytes :=
  ⟨include_bytes "../../../../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩
private def damaged : Bytes :=
  ⟨include_bytes "../../../../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v2-bad-length.parquet"⟩

private def retained := "label=caf%C3%A9%2fblue/year=%37/A%2Eparquet"
private def rejected := "year=8/B.parquet"
private def invalid := "year=8/label=%FF/invalid.parquet"
private def missing := "year=7/missing.parquet"

private def lookup (path : String) : Except String Bytes :=
  if path == retained then .ok clean
  else if path == rejected then .ok damaged
  else .error "missing snapshot"

private def keep : Scan.Predicate partitions.toScan Value :=
  fun row => (row ⟨0, by decide⟩).map (· == (7 : Int32))

private def zero : Scan.Projection (partitions.extend physical) := Scan.Projection.ofArray #[]
private def run (policy : OpenPolicy) :=
  scanPaths (partitions := partitions) (int32 := ordinal) (byteArray := payload) policy {} {} lookup zero keep

private def observes (policy : OpenPolicy) (budget : Nat) (paths : List String) (counts : List Nat)
    (outcome : Events.Termination (FileError (Int32ByteArray.Error String))) : Bool :=
  match run policy budget paths with
  | .error _ => false
  | .ok trace =>
    trace.batches.map (·.rowCount) == counts &&
      trace.rows.length == counts.sum && decide (trace.termination = outcome)

private def fails (policy : OpenPolicy) (budget : Nat) (paths : List String) (reason : Error) : Bool :=
  match run policy budget paths with
  | .error error => error == reason
  | .ok _ => false

private def invalidUtf8 : Error := .prepare (.partitionPath invalid .invalidUtf8)

#guard fails .strict 0 [retained, invalid] invalidUtf8
#guard fails .skipRejected 0 [retained, invalid] invalidUtf8
#guard fails .skipRejected 30 [missing, invalid] invalidUtf8

#guard observes .strict 0 [] [] .eos
#guard observes .strict 0 [retained] [] .closed
#guard observes .strict 1 [missing] [] (.readError (.open missing (.lookup "missing snapshot")))
#guard observes .strict 7 [retained, rejected, retained] [3, 0, 2] .closed
#guard observes .strict 8 [retained, rejected, retained] [3, 0, 2]
  (.readError (.source rejected (.parquet (.groupFailure 1
    (.byteArray (.page 1 1 "payload" 1 646 (.decode (.scalar (.plain .truncated)))))))))

#guard observes .skipRejected 0 [rejected] [] .eos
#guard observes .skipRejected 9 [retained, rejected, retained] [3, 0, 2, 3, 0, 2] .closed
#guard observes .skipRejected 10 [retained, rejected, retained] [3, 0, 2, 3, 0, 2] .eos
#guard observes .skipRejected 6 [retained, rejected, missing] [3, 0, 2]
  (.readError (.open missing (.lookup "missing snapshot")))

#print axioms scanPaths_error_iff
#print axioms scanPaths_ok_iff

end Silmaril.Formats.Hive.Manifest.Int32ByteArray.Ingress
