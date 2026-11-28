module

public import Silmaril.Formats.Relational.NamedTable.FromRenderedPositional.Defs
import Silmaril.Formats.Relational.NamedTable.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Hive Silmaril.Formats.Parquet
open Silmaril.Formats Silmaril.Formats.Relational
open TypedPartitions (PartitionSchema Convert)
open Int32ByteArrayGroup (Field)
open Int32ByteArrayGroup.File (Kind Value)

variable {Name : Type*} {Admission Failure : Type} {schema : Scan.Schema String Kind}

open Silmaril.Formats.Relational.NamedTable.FromRenderedPositional

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
        | .eos => .ok (Function.update db name (some ⟨schema, trace.rows⟩)) := by
  cases occupied : (db name).isSome
  · cases result with
    | error cause =>
      simp [importResult, NamedTable.importArrow, NamedTable.importCollected, toEventStream,
        Events.EventStream.collect, Except.map, occupied]
    | ok trace =>
      cases reached : trace.termination <;>
        simp [importResult, NamedTable.importArrow, NamedTable.importCollected, toEventStream,
          Events.EventStream.collect, Events.Trace.collect, Events.Trace.rows, Except.map, occupied, reached]
  · simp [importResult, NamedTable.importArrow, NamedTable.importCollected, occupied]

private theorem importResult_ok_iff [DecidableEq Name] (db next : Database Name) (name : Name)
    (result : ScanResult schema Admission Failure) :
    importResult db name result = .ok next ↔
      db name = none ∧ ∃ trace, result = .ok trace ∧ trace.termination = .eos ∧
        next = Function.update db name (some ⟨schema, trace.rows⟩) := by
  rw [importResult, NamedTable.importArrow_ok_iff]
  cases result with
  | error reason => simp [toEventStream, Events.EventStream.collect, Except.map]
  | ok trace =>
    cases reached : trace.termination <;>
      simp [toEventStream, Events.EventStream.collect, Except.map, Events.Trace.collect,
        Events.Trace.rows, reached, eq_comm]

variable {int32 byteArray : Field} {partitions : PartitionSchema Kind}

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
  importResult_ok_iff db next name _

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
      ∀ other, other ≠ name → next other = db other := by
  obtain ⟨_, trace, scanned, exhausted, rfl⟩ :=
    (importScan_ok_iff db next name admission maxDirectoryBytes keys encoding options convert listing
      limits lookup projection keep budget).mp loaded
  refine ⟨trace, scanned, exhausted, ?_, ?_, ?_⟩
  · simp [Scan.observePacked, Silmaril.Relational.Database.Packed.erase,
      Silmaril.Relational.Database.Partial.map]
  · simp [Events.Trace.rows, List.length_flatMap, Function.comp_def]
  · intro other different
    exact Function.update_of_ne different _ _

end Silmaril.Proofs.Formats.Relational.NamedTable.FromRenderedPositional
