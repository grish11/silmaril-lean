module

public import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.Defs
import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.RenderedPositional.Thms
import Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional

public section

namespace Silmaril.Formats.Relational.NamedTable.FromRenderedPositional

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Hive Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Name : Type*} {Admission Failure : Type} {schema : Scan.Schema String Kind}

/-- The exact source or destination error is returned without a database.
Only EOS at a vacant name yields the single-name update. -/
theorem importResult_outcome [DecidableEq Name] (db : Database Name) (name : Name)
    (result : ScanResult schema Admission Failure) :
    importResult db name result =
      if (db name).isSome then .error .nameConflict
      else match result with
      | .error reason => .error (.openError (.admission reason))
      | .ok trace =>
        match trace.termination with
        | .closed => .error .closed
        | .readError reason => .error (.readError (.runtime reason))
        | .closeError reason => .error (.closeError (.runtime reason))
        | .eos => .ok (Function.update db name (some ⟨schema, trace.rows⟩)) :=
  Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.importResult_outcome db name result

variable {int32 byteArray : Field} {partitions : PartitionSchema Kind}

/-- Success requires exhaustion and inserts exactly the projected
rows in trace order. The update is at the vacant name. -/
theorem importScan_ok_iff [DecidableEq Name] (db next : Database Name) (name : Name)
    (admission : Manifest.Inventory.Limits) (maxDirectoryBytes : Nat) (keys : List String)
    (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (convert : Convert Value Admission) (listing : List String) (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    importScan db name admission maxDirectoryBytes keys encoding options convert listing
      limits lookup projection keep budget = .ok next ↔
      db name = none ∧ ∃ trace,
        Manifest.RenderedPositional.scan admission maxDirectoryBytes keys encoding options convert listing
          limits lookup projection keep budget = .ok trace ∧ trace.termination = .eos ∧
        next = Function.update db name (some ⟨projection.schema, trace.rows⟩) :=
  Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.importScan_ok_iff
    db next name admission maxDirectoryBytes keys encoding options convert listing limits lookup projection keep budget

/-- The database observation keeps every projected row, including rows
with no cells, and every other database key keeps its original entry. -/
theorem importScan_observe [DecidableEq Name] (db next : Database Name) (name : Name)
    (admission : Manifest.Inventory.Limits) (maxDirectoryBytes : Nat) (keys : List String)
    (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (convert : Convert Value Admission) (listing : List String) (limits : Int32ByteArrayGroup.File.Limits)
    (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat)
    (loaded : importScan db name admission maxDirectoryBytes keys encoding options convert listing
      limits lookup projection keep budget = .ok next) :
    ∃ trace,
      Manifest.RenderedPositional.scan admission maxDirectoryBytes keys encoding options convert listing
        limits lookup projection keep budget = .ok trace ∧ trace.termination = .eos ∧
      Scan.observePacked next name = some ⟨projection.schema, trace.rows⟩ ∧
      trace.rows.length = (trace.batches.map AlignedColumns.rowCount).sum ∧
      ∀ other, other ≠ name → next other = db other :=
  Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional.importScan_observe
    db next name admission maxDirectoryBytes keys encoding options convert listing limits lookup projection keep budget loaded

/-- With the render witness, direct binding of the original entries,
stable literal ordering and pruning give the same atomic import result. -/
theorem importScan_eq_reference [DecidableEq Name] (db : Database Name) (name : Name)
    (admission : Manifest.Inventory.Limits) (renderLimits : PartitionPath.Positional.RenderLimits)
    (keys : List String) (encoding : PartitionPath.Positional.Encoding) (options : PartitionPath.Options)
    (convert : Convert Value Admission) (listing : List String) (original : String → PartitionPath.Partition)
    (witness : Manifest.RenderedPositional.MatchesRender admission renderLimits keys encoding options original listing)
    (limits : Int32ByteArrayGroup.File.Limits) (lookup : String → Except Failure Bytes)
    (projection : Scan.Projection (partitions.extend (Int32ByteArrayGroup.File.schema int32 byteArray)))
    (keep : Scan.Predicate partitions.toScan Value) (budget : Nat) :
    importScan db name admission renderLimits.maxDirectoryBytes keys encoding options convert listing
      limits lookup projection keep budget =
      importResult db name
        ((Manifest.prepareInventoryReferenceWith (Int32ByteArrayGroup.File.schema int32 byteArray) partitions
          admission (Manifest.RenderedPositional.fromOriginal renderLimits.maxDirectoryBytes original)
          options convert listing).map (fun files =>
            Manifest.scanInt32ByteArraySnapshotsBounded limits lookup projection keep budget
              ((Manifest.Inventory.orderFiles files).filter fun file => (keep file.cells).getD false))) := by
  unfold importScan
  rw [Manifest.RenderedPositional.scan_eq_reference admission renderLimits keys encoding options convert listing
    original witness limits lookup projection keep budget]

end Silmaril.Formats.Relational.NamedTable.FromRenderedPositional
