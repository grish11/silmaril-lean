module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Bounded.Defs
import Silmaril.Formats.Hive.ParquetScan.Thms
import Silmaril.Formats.Parquet.Reader.Pull.Thms
import Silmaril.Formats.Parquet.Snapshot.Pull.Thms
import Silmaril.Semantics.Relational.Scan.Thms
import Silmaril.Semantics.Relational.Table.Thms

public section

namespace Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot

open Silmaril.Relational Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Silmaril.Formats.Hive Silmaril.Formats.Hive.Manifest
open Silmaril.Formats.Hive.TypedPartitions (PartitionSchema extendRow)

variable {Kind Failure : Type*} {Value : Kind → Type*}
variable {physical : Scan.Schema String Kind} {schema : PartitionSchema Kind}

private theorem readFile_prefix (source : Reader.Source Nat physical Value (Snapshot.Error Failure))
    (pulls : Nat) (close : ∀ rest, source.close rest = .ok ()) :
    ParquetScan.readFile source pulls =
      let observed := Reader.denoteGroups source.readGroup (source.groups.take pulls)
      ⟨observed.1.map AlignedColumns.ofRows,
        match observed.2 with
        | .eos => if pulls ≤ source.groups.length then .closed else .eos
        | termination => termination⟩ := by
  have reader := Reader.read_prefix_opened
    (id : Reader.OpenResult Nat String Value (Snapshot.Error Failure) → _)
    (.ok ⟨physical, source⟩) pulls rfl
  rw [ParquetScan.readFile_eq_reader] at reader
  simp only [close, Except.ok.injEq, Sigma.mk.inj_iff, heq_iff_eq, true_and] at reader
  dsimp only
  cases outcome : (Reader.denoteGroups source.readGroup (source.groups.take pulls)).2 <;>
    simpa only [outcome] using reader

private theorem assemble_singleton (trace : Events.Trace physical Value (Snapshot.Error Failure)) :
    ParquetScan.assemble id [trace] = trace := by
  cases trace with
  | mk batches termination => cases termination <;> simp [ParquetScan.assemble]

private theorem project_group (projection : Scan.Projection (schema.extend physical))
    (cells : Scan.Row schema.toScan Value) (rows : Scan.Table physical Value) :
    projection.projectColumns
        (AlignedColumns.ofRows ((AlignedColumns.ofRows rows).toRows.map fun row => extendRow row cells)) =
      AlignedColumns.ofRows (projection.project (rows.map fun row => extendRow row cells)) := by
  apply AlignedColumns.rowsEquiv.symm.injective
  rw [projection.rowsEquiv_projectColumns]
  change projection.project (AlignedColumns.ofRows _).toRows = (AlignedColumns.ofRows _).toRows
  simp only [AlignedColumns.toRows_ofRows]

theorem scanSnapshotsBounded_eq_reference (limits : Snapshot.Limits) (lookup : String → Except Failure Bytes)
    (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value)
    (budget : Nat) (files : List (File schema Value)) :
    scanSnapshotsBounded limits lookup bind projection keep budget files =
      scanSnapshotsBoundedReference limits lookup bind projection keep budget files := by
  induction files generalizing budget with
  | nil => cases budget <;> rfl
  | cons file rest ih =>
    cases budget with
    | zero => rfl
    | succ pulls =>
      cases found : lookup file.path.declared with
      | error reason =>
        simp [scanSnapshotsBounded, scanSnapshotsBoundedReference, snapshotOpener, found]
      | ok bytes =>
        cases opened : Snapshot.openSource limits bind bytes with
        | error reason =>
          simp [scanSnapshotsBounded, scanSnapshotsBoundedReference, snapshotOpener, found, opened, Except.map]
        | ok source =>
          simp only [scanSnapshotsBounded, scanSnapshotsBoundedReference, snapshotOpener, found, opened,
            Except.map, scanFile, ParquetScan.scanPartition, assemble_singleton,
            readFile_prefix source pulls (Snapshot.openSource_close limits bind bytes opened)]
          simp only [ParquetScan.extendTrace, List.map_map, Function.comp_def, project_group]
          generalize groupsEq : Reader.denoteGroups source.readGroup (source.groups.take pulls) = groups
          rcases groups with ⟨rows, outcome⟩
          cases outcome with
          | eos =>
            by_cases exhausted : pulls ≤ source.groups.length <;>
              cases (keep file.cells).getD false <;> simp [exhausted, ih]
          | closed | readError _ | closeError _ =>
            cases (keep file.cells).getD false <;> rfl

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot
