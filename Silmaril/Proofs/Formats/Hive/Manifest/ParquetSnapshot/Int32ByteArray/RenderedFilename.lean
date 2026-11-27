module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedFilename.Defs
import Silmaril.Formats.Hive.Manifest.Inventory.Ordered.Scan.Thms
import Silmaril.Formats.Hive.PartitionPath.Filename.Render.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedFilename

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Hive Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.Manifest.RenderedFilename (MatchesRender)
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure AdmissionError : Type} {int32 byteArray : Field} {partitions : PartitionSchema Kind}

private theorem mapM_agree {α β ε : Type} (left right : α → Except ε β) (xs : List α)
    (agree : ∀ x ∈ xs, left x = right x) :
    xs.mapM left = xs.mapM right := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons, List.mapM_cons, agree x (by simp)]
    rw [ih (fun item member => agree item (List.mem_cons_of_mem _ member))]

private theorem reference_eq_original
    (physical : Scan.Schema String Kind) (admission : Inventory.Limits)
    (maxFilenameBytes : Nat) (keys : List String) (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (convert : Convert Value AdmissionError) (listing : List String) (original : String → PartitionPath.Partition)
    (witness : MatchesRender admission maxFilenameBytes keys encoding options original listing) :
    prepareInventoryReferenceWithFileParser physical partitions admission (PartitionPath.Filename.parse maxFilenameBytes keys encoding)
        options convert listing =
      prepareInventoryReferenceWithFileParser physical partitions admission
        (fun _ _ leaf => .ok (original leaf)) options convert listing := by
  unfold prepareInventoryReferenceWithFileParser
  split
  · rfl
  · unfold Inventory.referenceFromWithFileParser
    congr 1
    apply mapM_agree
    intro ⟨path, index⟩ member
    have included : path ∈ listing.take admission.maxEntries := List.fst_mem_of_mem_zipIdx member
    by_cases fits : path.utf8ByteSize ≤ admission.maxPathBytes
    · cases lexical : splitFile path with
      | error reason => simp [Inventory.checkEntryWithFileParser, Nat.not_lt.mpr fits, lexical]
      | ok parts =>
        obtain ⟨parent, leaf⟩ := parts
        cases control : Inventory.isControlLeaf leaf
        · obtain ⟨suffix, rendered⟩ := witness path included fits parent leaf lexical control
          simp [Inventory.checkEntryWithFileParser, Nat.not_lt.mpr fits, lexical, control,
            prepareFileWithFileParser, Except.bind, Except.mapError, PartitionPath.Filename.parse_render_of_ok rendered parent]
        · simp [Inventory.checkEntryWithFileParser, Nat.not_lt.mpr fits, lexical, control]
    · simp [Inventory.checkEntryWithFileParser, Nat.lt_of_not_ge fits]

theorem scan_eq_reference
    (admission : Inventory.Limits) (maxFilenameBytes : Nat) (keys : List String)
    (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (convert : Convert Value AdmissionError) (listing : List String)
    (original : String → PartitionPath.Partition)
    (witness : MatchesRender admission maxFilenameBytes keys encoding options original listing)
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    Manifest.RenderedFilename.scan admission maxFilenameBytes keys encoding options convert listing
      limits lookup projection keep budget =
      (prepareInventoryReferenceWithFileParser (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
        admission (fun _ _ leaf => .ok (original leaf)) options convert listing).map (fun files =>
          scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget
            ((Inventory.orderFiles files).filter fun file => (keep file.cells).getD false)) := by
  unfold Manifest.RenderedFilename.scan
  rw [prepareOrderedInventoryWithFileParser_scanSkippingRejected_eq_reference,
    reference_eq_original _ admission maxFilenameBytes keys encoding options convert listing original witness]

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedFilename
