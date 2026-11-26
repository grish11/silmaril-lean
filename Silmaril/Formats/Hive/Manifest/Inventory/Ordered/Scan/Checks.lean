module

import Silmaril.Data.IncludeBytes
import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Scan.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Bounded.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Thms
meta import Silmaril.Data.IncludeBytes
meta import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
meta import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Pruning.Defs

namespace Silmaril.Formats.Hive.Manifest

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet Silmaril.Relational
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)
open TypedPartitions (PartitionSchema)

private def ordinal : Field := ⟨"ordinal", .required⟩
private def payload : Field := ⟨"payload", .optional⟩
private def physical := Int32ByteArrayGroup.File.schema ordinal payload
private def partitions : PartitionSchema Kind := ⟨#[⟨"year", .int32 .optional, .reject⟩]⟩
private def keep : Scan.Predicate partitions.toScan Value :=
  fun row => (row ⟨0, by decide⟩).map (· != (9 : Int32))
private def projection : Scan.Projection (partitions.extend physical) :=
  Scan.Projection.ofArray #[⟨2, by decide⟩]
private def zero : Scan.Projection (partitions.extend physical) := Scan.Projection.ofArray #[]

private def clean := "year=%37/A%2Eparquet"
private def corrupt := "year=7/C.parquet"
private def missing := "year=7/Z.parquet"
private def rejected := "year=%39/rejected.parquet"
private def malformed := "year=%39/%FF/Malformed.parquet"

private def cleanBytes : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-int32-byte-array-file/empty-middle-v2.parquet"⟩
private def corruptBytes : Bytes :=
  ⟨include_bytes "../../../../../../../data/parquet-plain-byte-array-file/plain-byte-array-v2-bad-length.parquet"⟩

private def lookup (path : String) : Except String Bytes :=
  if path == clean then .ok cleanBytes
  else if path == corrupt then .ok corruptBytes
  else .error "missing snapshot"

private def lookupWithRejected (path : String) : Except String Bytes :=
  if path == rejected then .ok corruptBytes else lookup path

private def admit := prepareOrderedInventory physical partitions ⟨10, 128⟩ {} Int32ByteArray.Ingress.convert
private abbrev RuntimeError := FileError (Int32ByteArray.Error String)

private def scanZero (resolve : String → Except String Bytes) (budget : Nat) (paths : List String) :
    Except (Inventory.Error Int32ByteArray.Ingress.CastError) (Events.Trace zero.schema Value RuntimeError) :=
  (admit paths).map (scanInt32ByteArraySnapshotsBoundedSkippingRejected {} resolve zero keep budget)

private def observes (resolve : String → Except String Bytes) (budget : Nat) (paths : List String)
    (counts : List Nat) (outcome : Events.Termination RuntimeError) : Bool :=
  match scanZero resolve budget paths with
  | .error _ => false
  | .ok trace =>
    trace.batches.map (·.rowCount) == counts && trace.rows.length == counts.sum &&
      decide (trace.termination = outcome)

private def corruption : Events.Termination RuntimeError :=
  .readError (.source corrupt (.parquet (.groupFailure 1
    (.byteArray (.page 1 1 "payload" 1 646 (.decode (.scalar (.plain .truncated))))))))

private def listing := [missing, corrupt, clean, rejected, clean]

#guard (admit listing).toOption.map (List.map (·.path.declared)) ==
  some [clean, clean, rejected, corrupt, missing]
#guard observes lookup 0 [rejected] [] .eos
#guard observes lookupWithRejected 9 [rejected, clean, clean] [3, 0, 2, 3, 0, 2] .closed
#guard observes lookupWithRejected 10 [rejected, clean, clean] [3, 0, 2, 3, 0, 2] .eos
#guard observes lookup 12 listing [3, 0, 2, 3, 0, 2, 12] .closed
#guard observes lookup 13 listing [3, 0, 2, 3, 0, 2, 12] corruption
#guard observes lookupWithRejected 13 listing [3, 0, 2, 3, 0, 2, 12] corruption
#guard observes lookup 6 [missing, rejected, clean] [3, 0, 2]
  (.readError (.open missing (.lookup "missing snapshot")))
#guard match scanZero lookup 0 [clean, malformed, missing] with
  | .error reason => reason == .entry 1 (.partitionPath malformed (.missingEquals "%FF"))
  | .ok _ => false

#guard match admit listing with
  | .error _ => false
  | .ok files =>
    let ordinalOnly : Scan.Projection (partitions.extend physical) :=
      Scan.Projection.ofArray #[⟨0, by decide⟩]
    let trace := scanInt32ByteArraySnapshotsBoundedSkippingRejected {} lookup ordinalOnly keep 13 files
    let cleanRows : List (Option Int32) := [some (-2147483648), some 0, some 17, some 2147483647, some (-1)]
    trace.rows.map (fun row => row ⟨0, by decide⟩) ==
      cleanRows ++ cleanRows ++ (List.range 12).map (some ∘ Int32.ofNat) &&
      decide (trace.termination = corruption)

-- Equal literal keys with different virtual cells stay in supplied tie order.
private def tied (year : Int32) : File partitions Value :=
  ⟨⟨clean, "year=7", "A%2Eparquet"⟩, Fin.cases (some year) (fun i => nomatch i)⟩

private def observeTies (files : List (File partitions Value)) : List (Option Int32) :=
  let trace := scanInt32ByteArraySnapshotsBoundedSkippingRejected {} lookup projection keep 10
    (Inventory.orderFiles files)
  trace.rows.map (fun row => row ⟨0, by decide⟩)

#guard observeTies [tied 1, tied 2] == List.replicate 5 (some 1) ++ List.replicate 5 (some 2)
#guard observeTies [tied 2, tied 1] == List.replicate 5 (some 2) ++ List.replicate 5 (some 1)

#print axioms scanBounded_congr_opener
#print axioms int32ByteArraySnapshotOpener_congr_lookup
#print axioms prepareOrderedInventory_scanSkippingRejected_eq_reference
#print axioms scanOrderedSkippingRejected_congr_lookup

end Silmaril.Formats.Hive.Manifest
