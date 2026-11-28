module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedFilename.Defs
import Silmaril.Formats.Hive.PartitionPath.Filename.Render.Thms
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Bounded.Thms
import Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedFilename

public section

namespace Silmaril.Formats.Hive.Manifest.RenderedFilename

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Failure AdmissionError : Type} {int32 byteArray : Field}
variable {partitions : PartitionSchema Kind}

/-- A rendered leaf binds the original entries and keeps the supplied lookup
path, including its parent and the exact percent spelling. -/
theorem prepareFile_of_render {maxFilenameBytes : Nat} {keys : List String} {encoding : PartitionPath.Positional.Encoding}
    {options : PartitionPath.Options} {entries : PartitionPath.Partition}
    {suffix parent leaf path canonical : String} (convert : Convert Value AdmissionError)
    {cells : Scan.Row partitions.toScan Value}
    (lexical : splitFile path = .ok (parent, leaf))
    (rendered : PartitionPath.Filename.render maxFilenameBytes keys encoding options entries suffix = .ok leaf)
    (normalized : PartitionPath.render options entries = .ok canonical)
    (decoded : TypedPartitions.decode partitions convert entries = .ok cells) :
    prepareFileWithFileParser partitions (PartitionPath.Filename.parse maxFilenameBytes keys encoding) options convert path =
      .ok ⟨⟨path, canonical, leaf⟩, cells⟩ := by
  simp [prepareFileWithFileParser, lexical, PartitionPath.Filename.parse_render_of_ok rendered parent, normalized, decoded,
    Except.bind, Except.map, Except.mapError]

/-- Exact bounded trace against the original entries that produced the
filenames. The reference binds those entries directly, then stably orders
and filters the records before the existing bounded traversal. -/
theorem scan_eq_reference
    (admission : Inventory.Limits) (maxFilenameBytes : Nat) (keys : List String)
    (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (convert : Convert Value AdmissionError) (listing : List String)
    (original : String → PartitionPath.Partition)
    (witness : MatchesRender admission maxFilenameBytes keys encoding options original listing)
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    scan admission maxFilenameBytes keys encoding options convert listing limits lookup projection keep budget =
      (prepareInventoryReferenceWithFileParser (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
        admission (fun _ _ leaf => .ok (original leaf)) options convert listing).map (fun files =>
          scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget
            ((Inventory.orderFiles files).filter fun file => (keep file.cells).getD false)) :=
  Proofs.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedFilename.scan_eq_reference
    admission maxFilenameBytes keys encoding options convert listing original witness limits lookup projection keep budget

/-- With enough actions, the full trace is the checked row-group denotation
over the original typed entries, with the same virtual filter, projection,
aligned batches and first retained failure. -/
theorem scan_eq_denotation_of_cost
    (admission : Inventory.Limits) (maxFilenameBytes : Nat) (keys : List String)
    (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (convert : Convert Value AdmissionError) (listing : List String)
    (original : String → PartitionPath.Partition)
    (witness : MatchesRender admission maxFilenameBytes keys encoding options original listing)
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) {budget actions : Nat} {files : List (File partitions Value)}
    (admitted : prepareInventoryReferenceWithFileParser (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
      admission (fun _ _ leaf => .ok (original leaf)) options convert listing = .ok files)
    (cost : Int32ByteArrayScanCost limits int32 byteArray lookup
      ((Inventory.orderFiles files).filter fun file => (keep file.cells).getD false) actions)
    (enough : actions ≤ budget) :
    scan admission maxFilenameBytes keys encoding options convert listing limits lookup projection keep budget =
      .ok (denoteInt32ByteArraySnapshots limits lookup projection keep
        ((Inventory.orderFiles files).filter fun file => (keep file.cells).getD false)) := by
  rw [scan_eq_reference admission maxFilenameBytes keys encoding options convert listing original witness,
    admitted]
  exact congrArg Except.ok (scanInt32ByteArraySnapshotsBounded_eq_reference_of_cost limits lookup projection keep cost enough)

end Silmaril.Formats.Hive.Manifest.RenderedFilename
