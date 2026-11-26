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

private theorem denoteGroups_append_of_decoded
    (read : Nat → Except (Snapshot.Error Failure) (Reader.RowGroup physical Value))
    (before after : List Nat) {rows : List (Reader.RowGroup physical Value)}
    (decoded : before.mapM read = .ok rows) :
    Reader.denoteGroups read (before ++ after) =
      (rows ++ (Reader.denoteGroups read after).1, (Reader.denoteGroups read after).2) := by
  induction before generalizing rows with
  | nil =>
    have equal : [] = rows := Except.ok.inj decoded
    subst rows
    simp
  | cons group rest ih =>
    cases head : read group with
    | error reason =>
      simp [List.mapM_cons, head, bind, Except.bind] at decoded
    | ok groupRows =>
      cases tail : rest.mapM read with
      | error reason =>
        simp [List.mapM_cons, head, tail, bind, Except.bind] at decoded
      | ok remaining =>
        have equal : groupRows :: remaining = rows := by
          simpa [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure] using decoded
        subst rows
        simp [Reader.denoteGroups, head, ih tail]

private theorem readFile_of_decoded (source : Reader.Source Nat physical Value (Snapshot.Error Failure))
    (close : ∀ rest, source.close rest = .ok ()) {pulls : Nat}
    (enough : source.groups.length < pulls) {rows : List (Reader.RowGroup physical Value)}
    (decoded : source.groups.mapM source.readGroup = .ok rows) :
    ParquetScan.readFile source pulls = ⟨rows.map AlignedColumns.ofRows, .eos⟩ := by
  have observed := denoteGroups_append_of_decoded source.readGroup source.groups [] decoded
  rw [List.append_nil] at observed
  simp [readFile_prefix source pulls close, List.take_of_length_le (Nat.le_of_lt enough), observed,
    Reader.denoteGroups, Nat.not_le_of_gt enough]

private theorem readFile_through_failure (source : Reader.Source Nat physical Value (Snapshot.Error Failure))
    (close : ∀ rest, source.close rest = .ok ()) {pulls group : Nat} {before after : List Nat}
    {rows : List (Reader.RowGroup physical Value)} {reason : Snapshot.Error Failure}
    (split : source.groups = before ++ group :: after) (enough : before.length < pulls)
    (decoded : before.mapM source.readGroup = .ok rows) (failed : source.readGroup group = .error reason) :
    ParquetScan.readFile source pulls = ⟨rows.map AlignedColumns.ofRows, .readError reason⟩ := by
  have pullsLeft : pulls - before.length = (pulls - before.length - 1) + 1 := by omega
  rw [readFile_prefix source pulls close, split, List.take_append,
    List.take_of_length_le (Nat.le_of_lt enough), pullsLeft, List.take_succ_cons,
    denoteGroups_append_of_decoded source.readGroup before _ decoded]
  simp [Reader.denoteGroups, failed]

theorem scanSnapshotsBounded_eq_scan_of_cost (limits : Snapshot.Limits) (lookup : String → Except Failure Bytes)
    (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value)
    {budget actions : Nat} {files : List (File schema Value)}
    (cost : SnapshotScanCost limits lookup bind files actions) (enough : actions ≤ budget) :
    scanSnapshotsBounded limits lookup bind projection keep budget files =
      scan (snapshotOpener limits lookup bind) projection keep files := by
  induction cost generalizing budget with
  | nil => cases budget <;> rfl
  | openError failed =>
    cases budget with
    | zero => omega
    | succ pulls =>
      simp [scanSnapshotsBounded, scan, ParquetScan.assemble, scanFile, failed]
  | @complete file rest bytes source rows actions found opened decoded tail ih =>
    cases budget with
    | zero => omega
    | succ pulls =>
      have close := Snapshot.openSource_close limits bind bytes opened
      have current := readFile_of_decoded source close (pulls := pulls) (by omega) decoded
      have full := readFile_of_decoded source close (pulls := source.groups.length + 1) (by omega) decoded
      have later := ih (budget := pulls - (source.groups.length + 1)) (by omega)
      simp [scanSnapshotsBounded, scan, ParquetScan.assemble, scanFile, snapshotOpener, found,
        opened, Except.map, current, full, ParquetScan.scanPartition, later]
      cases (keep file.cells).getD false <;> rfl
  | @readError file rest bytes source before group after rows reason found opened split decoded failed =>
    cases budget with
    | zero => omega
    | succ pulls =>
      have close := Snapshot.openSource_close limits bind bytes opened
      have less : before.length < source.groups.length + 1 := by simp [split]; omega
      have current := readFile_through_failure source close split (pulls := pulls) (by omega) decoded failed
      have full := readFile_through_failure source close split less decoded failed
      simp [scanSnapshotsBounded, scan, ParquetScan.assemble, scanFile, snapshotOpener, found,
        opened, Except.map, current, full, ParquetScan.scanPartition]
      cases (keep file.cells).getD false <;> rfl

private theorem group_read_outcome
    (read : Nat → Except (Snapshot.Error Failure) (Reader.RowGroup physical Value)) (groups : List Nat) :
    (∃ rows, groups.mapM read = .ok rows) ∨
      ∃ before group after rows reason, groups = before ++ group :: after ∧
        before.mapM read = .ok rows ∧ read group = .error reason := by
  induction groups with
  | nil => exact .inl ⟨[], rfl⟩
  | cons group rest ih =>
    cases head : read group with
    | error reason => exact .inr ⟨[], group, rest, [], reason, rfl, rfl, head⟩
    | ok rows =>
      rcases ih with ⟨later, decoded⟩ | ⟨before, failedGroup, after, earlier, reason, split, decoded, failed⟩
      · exact .inl ⟨rows :: later, by simp [List.mapM_cons, head, decoded, bind, Except.bind, pure, Except.pure]⟩
      · exact .inr ⟨group :: before, failedGroup, after, rows :: earlier, reason,
          congrArg (group :: ·) split,
          by simp [List.mapM_cons, head, decoded, bind, Except.bind, pure, Except.pure], failed⟩

theorem snapshotScanCost_exists (limits : Snapshot.Limits) (lookup : String → Except Failure Bytes)
    (bind : Snapshot.Bind physical Value Failure) (files : List (File schema Value)) :
    ∃ actions, SnapshotScanCost limits lookup bind files actions := by
  induction files with
  | nil => exact ⟨0, .nil⟩
  | cons file rest ih =>
    cases found : lookup file.path.declared with
    | error reason =>
      exact ⟨1, .openError (reason := .input reason) (by simp [snapshotOpener, found])⟩
    | ok bytes =>
      cases opened : Snapshot.openSource limits bind bytes with
      | error reason =>
        exact ⟨1, .openError (reason := reason) (by simp [snapshotOpener, found, opened, Except.map])⟩
      | ok source =>
        rcases group_read_outcome source.readGroup source.groups with
          ⟨rows, decoded⟩ | ⟨before, group, after, rows, reason, split, decoded, failed⟩
        · obtain ⟨actions, tail⟩ := ih
          exact ⟨_, .complete found opened decoded tail⟩
        · exact ⟨_, .readError found opened split decoded failed⟩

private theorem denoteGroups_take_of_decoded
    (read : Nat → Except (Snapshot.Error Failure) (Reader.RowGroup physical Value))
    (indices : List Nat) {rows : List (Reader.RowGroup physical Value)}
    (decoded : indices.mapM read = .ok rows) (pulls : Nat) :
    Reader.denoteGroups read (indices.take pulls) = (rows.take pulls, .eos) := by
  induction indices generalizing rows pulls with
  | nil =>
    have equal : [] = rows := Except.ok.inj decoded
    subst rows
    simp [Reader.denoteGroups]
  | cons index rest ih =>
    cases pulls with
    | zero => rfl
    | succ pulls =>
      cases head : read index with
      | error reason => simp [List.mapM_cons, head, bind, Except.bind] at decoded
      | ok groupRows =>
        cases tail : rest.mapM read with
        | error reason => simp [List.mapM_cons, head, tail, bind, Except.bind] at decoded
        | ok remaining =>
          have equal : groupRows :: remaining = rows := by
            simpa [List.mapM_cons, head, tail, bind, Except.bind, pure, Except.pure] using decoded
          subst rows
          simp [Reader.denoteGroups, head, ih tail]

private theorem readFile_within_decoded
    (source : Reader.Source Nat physical Value (Snapshot.Error Failure))
    (close : ∀ rest, source.close rest = .ok ()) {before after : List Nat} {pulls : Nat}
    {rows : List (Reader.RowGroup physical Value)}
    (split : source.groups = before ++ after) (within : pulls ≤ before.length)
    (decoded : before.mapM source.readGroup = .ok rows) :
    ParquetScan.readFile source pulls = ⟨(rows.take pulls).map AlignedColumns.ofRows, .closed⟩ := by
  have exhausted : pulls ≤ source.groups.length := by simpa [split] using Nat.le_add_right_of_le within
  have denoted : Reader.denoteGroups source.readGroup (source.groups.take pulls) =
      (rows.take pulls, .eos) := by
    rw [split, List.take_append_of_le_length within, denoteGroups_take_of_decoded _ _ decoded]
  simp [readFile_prefix source pulls close, denoted, exhausted]

theorem scanSnapshotsBounded_exact_boundary (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value)
    {budget actions : Nat} {files : List (File schema Value)}
    (cost : SnapshotScanCost limits lookup bind files actions) :
    let bounded := scanSnapshotsBounded limits lookup bind projection keep budget files
    let strict := scan (snapshotOpener limits lookup bind) projection keep files
    (bounded.termination = .closed ↔ budget < actions) ∧ List.IsPrefix bounded.batches strict.batches := by
  induction cost generalizing budget with
  | nil =>
    cases budget <;> simp [scanSnapshotsBounded, scan, ParquetScan.assemble]
  | openError failed =>
    cases budget <;> simp [scanSnapshotsBounded, scan, ParquetScan.assemble, scanFile, failed]
  | @complete file rest bytes source rows actions found opened decoded tail ih =>
    cases budget with
    | zero =>
      simp [scanSnapshotsBounded]
      omega
    | succ pulls =>
      have close := Snapshot.openSource_close limits bind bytes opened
      have full := readFile_of_decoded source close (pulls := source.groups.length + 1) (by omega) decoded
      by_cases within : pulls ≤ source.groups.length
      · have short : pulls + 1 < source.groups.length + 2 + actions := by omega
        have prefixRead := readFile_within_decoded source close (after := []) (List.append_nil _).symm within decoded
        cases kept : (keep file.cells).getD false
        · simp [scanSnapshotsBounded, snapshotOpener, found, opened, Except.map,
            scanFile, ParquetScan.scanPartition, prefixRead, assemble_singleton, kept, short]
        · simp [scanSnapshotsBounded, scan, ParquetScan.assemble, snapshotOpener, found, opened, Except.map,
            scanFile, ParquetScan.scanPartition, ParquetScan.extendTrace, prefixRead, full, kept, short,
            List.prefix_append_of_prefix (List.take_prefix ..)]
      · have current := readFile_of_decoded source close (pulls := pulls) (Nat.lt_of_not_ge within) decoded
        have later := ih (budget := pulls - (source.groups.length + 1))
        have short : pulls - (source.groups.length + 1) < actions ↔
            pulls + 1 < source.groups.length + 2 + actions := by omega
        cases kept : (keep file.cells).getD false <;>
          simpa [scanSnapshotsBounded, scan, ParquetScan.assemble, snapshotOpener, found, opened, Except.map,
            scanFile, ParquetScan.scanPartition, current, full, kept, short] using later
  | @readError file rest bytes source before group after rows reason found opened split decoded failed =>
    cases budget with
    | zero => simp [scanSnapshotsBounded]
    | succ pulls =>
      have close := Snapshot.openSource_close limits bind bytes opened
      have reached : before.length < source.groups.length + 1 := by simp [split]; omega
      have full := readFile_through_failure source close split reached decoded failed
      by_cases within : pulls ≤ before.length
      · have short : pulls + 1 < before.length + 2 := by omega
        have prefixRead := readFile_within_decoded source close split within decoded
        cases kept : (keep file.cells).getD false <;>
          simp [scanSnapshotsBounded, scan, ParquetScan.assemble, snapshotOpener, found, opened, Except.map,
            scanFile, ParquetScan.scanPartition, ParquetScan.extendTrace, prefixRead, full, kept, short, List.take_prefix]
      · have short : ¬ pulls + 1 < before.length + 2 := by omega
        have current := readFile_through_failure source close split (Nat.lt_of_not_ge within) decoded failed
        cases kept : (keep file.cells).getD false <;>
          simp [scanSnapshotsBounded, scan, ParquetScan.assemble, snapshotOpener, found, opened, Except.map,
            scanFile, ParquetScan.scanPartition, current, full, kept, short]

theorem scanSnapshotsBounded_append_of_stopped (limits : Snapshot.Limits)
    (lookup : String → Except Failure Bytes) (bind : Snapshot.Bind physical Value Failure)
    (projection : Scan.Projection (schema.extend physical)) (keep : Scan.Predicate schema.toScan Value)
    (budget : Nat) (files suffix : List (File schema Value))
    (stopped : (scanSnapshotsBounded limits lookup bind projection keep budget files).termination ≠ .eos) :
    scanSnapshotsBounded limits lookup bind projection keep budget (files ++ suffix) =
      scanSnapshotsBounded limits lookup bind projection keep budget files := by
  induction files generalizing budget with
  | nil =>
    cases budget <;> simp [scanSnapshotsBounded] at stopped
  | cons file rest ih =>
    cases budget with
    | zero => rfl
    | succ pulls =>
      cases opened : snapshotOpener limits lookup bind file.path.declared with
      | error reason => simp [scanSnapshotsBounded, opened]
      | ok source =>
        cases outcome :
            (scanFile (fun _ => .ok { source with fuel := pulls }) projection keep file).termination with
        | eos =>
          have tailStop :
              (scanSnapshotsBounded limits lookup bind projection keep (pulls - source.fuel) rest).termination ≠ .eos := by
            simpa [scanSnapshotsBounded, opened, outcome] using stopped
          simp [scanSnapshotsBounded, opened, outcome, ih _ tailStop]
        | closed | readError _ | closeError _ =>
          simp [scanSnapshotsBounded, opened, outcome]

end Silmaril.Proofs.Formats.Hive.Manifest.ParquetSnapshot
