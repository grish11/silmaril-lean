module

public import Silmaril.Machine.SqliteVfs.TrackA.Write.Defs
import Silmaril.Machine.SqliteVfs.Thms
import Silmaril.Formats.Sqlite.File.WriteProfile.Reopen.Thms
import Silmaril.Formats.Sqlite.File.WriteProfile.Thms
import Silmaril.Formats.Sqlite.WriteProfile.Thms
import Silmaril.Proofs.Machine.SqliteVfs.TrackA.Write.Correspondence

public section

namespace Silmaril.Proofs.Machine.SqliteVfs.TrackA.Write

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SqliteVfs.TrackA.Write
open Silmaril.Formats.Sqlite
open Silmaril.Formats.Sqlite.WriteProfile (Edited Row)

variable {op : Insert} {vm : Vdbe.State} {ctx : Context} {id amount : Int64}
variable {edited : Edited} {catalogue newPage : Silmaril.Machine.SqliteVfs.Bytes}
variable {limits : Limits}

private def recordedFiles (ctx : Context) (catalogue : Silmaril.Machine.SqliteVfs.Bytes) : Files :=
  { initialFiles ctx catalogue with journal := some (openWritable ctx.journalHandle ctx.oldPage) }

private theorem write_openWritable (handle : Handle)
    (old bytes : Silmaril.Machine.SqliteVfs.Bytes) (offset : Int) (capacity : Nat)
    (range : WriteRange offset bytes.length) (fits : offset.toNat + bytes.length ≤ capacity) :
    readWrite capacity (openWritable handle old) (.write handle offset bytes) =
      (.ok (), openWritable handle (overwrite old offset.toNat bytes)) := by
  have law := (readWrite_lawful capacity).2.2.write (openWritable handle old) handle offset bytes
  simpa [openWritable, FileState.mode, range, fits, Prod.ext_iff] using law

private theorem write_journal (fault : Option Silmaril.Machine.SqliteVfs.Error)
    (oldLength : ctx.oldPage.length = 512) (journalCapacity : 512 ≤ limits.journal) :
    dispatch limits fault (initialFiles ctx catalogue) (.write .journal ctx.journalHandle 0 ctx.oldPage) =
      (.ok (), recordedFiles ctx catalogue) := by
  have range : WriteRange 0 ctx.oldPage.length := by rw [oldLength]; decide
  have fits : (0 : Int).toNat + ctx.oldPage.length ≤ limits.journal := by
    simpa [oldLength] using journalCapacity
  have write := write_openWritable ctx.journalHandle [] ctx.oldPage 0 limits.journal range fits
  simp [dispatch, initialFiles, recordedFiles, write, overwrite]

private theorem sync_journal (fault : Option Silmaril.Machine.SqliteVfs.Error) :
    dispatch limits fault (recordedFiles ctx catalogue) (.sync .journal ctx.journalHandle) =
      (fault.elim (.ok ()) Except.error, recordedFiles ctx catalogue) := by
  simp [dispatch, recordedFiles, openWritable, FileState.mode]
  rfl

private theorem overwrite_leaf (catLength : catalogue.length = 512)
    (oldLength : ctx.oldPage.length = 512) (newLength : newPage.length = 512) :
    overwrite (catalogue ++ ctx.oldPage) 512 newPage = catalogue ++ newPage := by
  have prefixEq : (catalogue ++ ctx.oldPage).take 512 = catalogue := by
    simpa only [catLength] using (List.take_append_length (l₁ := catalogue) (l₂ := ctx.oldPage))
  have suffixEq : (catalogue ++ ctx.oldPage).drop (512 + newPage.length) = [] :=
    List.drop_eq_nil_of_le (by simp [catLength, oldLength, newLength])
  simp [overwrite, prefixEq, suffixEq, catLength, oldLength]

private theorem write_database (catLength : catalogue.length = 512)
    (oldLength : ctx.oldPage.length = 512) (newLength : newPage.length = 512)
    (databaseCapacity : 1024 ≤ limits.database) :
    dispatch limits none (recordedFiles ctx catalogue) (.write .database ctx.databaseHandle 512 newPage) =
      (.ok (), { recordedFiles ctx catalogue with
        database := openWritable ctx.databaseHandle (catalogue ++ newPage) }) := by
  have range : WriteRange 512 newPage.length := by rw [newLength]; decide
  have fits : (512 : Int).toNat + newPage.length ≤ limits.database := by
    simpa [newLength] using databaseCapacity
  have write := write_openWritable ctx.databaseHandle (catalogue ++ ctx.oldPage)
    newPage 512 limits.database range fits
  have bytes := overwrite_leaf (ctx := ctx) (newPage := newPage) catLength oldLength newLength
  simp [dispatch, recordedFiles, initialFiles, write, bytes]

theorem commit_success
    (vmOperands : op.operands vm ctx = .ok (id, amount))
    (inserted : ctx.snapshot.apply (.insert (.integer id) (.integer amount)) = .ok edited)
    (resident : WriteProfile.Image.tablePage ctx.snapshot = .ok ctx.oldPage)
    (catalogueOk : WriteProfile.Image.cataloguePage = .ok catalogue)
    (packed : WriteProfile.Image.tablePage edited.snapshot = .ok newPage)
    (journalCapacity : 512 ≤ limits.journal) (databaseCapacity : 1024 ≤ limits.database) :
    let run := (insertAndCommit op vm ctx).run (dispatch limits) (initialFiles ctx catalogue)
    run.events = completed ctx newPage ∧
      run.result = .ok ⟨{ vm.advance with halted := some 0 }, edited.snapshot, 1⟩ ∧
      run.files = ⟨openWritable ctx.databaseHandle (catalogue ++ newPage), none⟩ ∧
      TableLeaf.open? (Silmaril.Formats.Bytes.ofList run.files.database.bytes) =
        some edited.snapshot.readTable ∧
      edited.snapshot.rows = ⟨id, amount⟩ :: ctx.snapshot.rows := by
  have prepared := prepareLeaf_ok inserted packed
  have oldLength := WriteProfile.Image.leaf_length resident
  have newLength := WriteProfile.Image.leaf_length packed
  have catLength := WriteProfile.Image.leaf_length catalogueOk
  have journalWrite := write_journal (catalogue := catalogue) none oldLength journalCapacity
  have journalSync : dispatch limits none (recordedFiles ctx catalogue)
      (.sync .journal ctx.journalHandle) = (.ok (), recordedFiles ctx catalogue) :=
    sync_journal none
  let written := { recordedFiles ctx catalogue with
    database := openWritable ctx.databaseHandle (catalogue ++ newPage) }
  have dbWrite : dispatch limits none (recordedFiles ctx catalogue)
      (.write .database ctx.databaseHandle ((512 : Nat) : Int) newPage) = (.ok (), written) :=
    write_database catLength oldLength newLength databaseCapacity
  have dbSync : dispatch limits none written (.sync .database ctx.databaseHandle) =
      (.ok (), written) := by
    simp [dispatch, written, openWritable, FileState.mode]
  have delete : dispatch limits none written (.deleteJournal ctx.journalHandle) =
      (.ok (), { written with journal := none }) := by
    simp [dispatch, written, recordedFiles, openWritable, FileState.mode]
  have image : WriteProfile.Image.encode edited.snapshot =
      .ok (Silmaril.Formats.Bytes.ofList (catalogue ++ newPage)) := by
    simp [WriteProfile.Image.encode, catalogueOk, packed]
  obtain ⟨rows, changed⟩ := WriteProfile.insert_rows ctx.snapshot inserted
  simp only [insertAndCommit, vmOperands, btreeInsert, prepared, Pager.admit, Pager.phaseOne,
    Pager.phaseTwo, Context.page, PageRead.Page.offset, File.Write.pageSize, Nat.reduceSub,
    Nat.reduceMul, issue, Program.run.eq_1, Program.run.eq_2, Program.run.eq_3, journalWrite,
    journalSync, dbWrite, dbSync, delete]
  exact ⟨rfl, by rw [changed], rfl, WriteProfile.Image.encode_open_table image, rows⟩

theorem journal_sync_failure {reason : Silmaril.Machine.SqliteVfs.Error}
    (vmOperands : op.operands vm ctx = .ok (id, amount))
    (prepared : prepareLeaf ctx id amount = .ok (edited, newPage))
    (resident : WriteProfile.Image.tablePage ctx.snapshot = .ok ctx.oldPage)
    (journalCapacity : 512 ≤ limits.journal) :
    let run := (insertAndCommit op vm ctx).run (dispatch limits (some reason)) (initialFiles ctx catalogue)
    run.events =
      [⟨Call.write .journal ctx.journalHandle 0 ctx.oldPage, .ok ()⟩,
       ⟨Call.sync .journal ctx.journalHandle, .error reason⟩] ∧
    run.result = .error (.vfs .syncJournal reason) ∧
    run.files.database = (initialFiles ctx catalogue).database ∧
    run.files.journal = some (openWritable ctx.journalHandle ctx.oldPage) := by
  have journalWrite := write_journal (catalogue := catalogue) (some reason)
    (WriteProfile.Image.leaf_length resident) journalCapacity
  have journalSync : dispatch limits (some reason) (recordedFiles ctx catalogue)
      (.sync .journal ctx.journalHandle) = (.error reason, recordedFiles ctx catalogue) :=
    sync_journal (some reason)
  simp only [insertAndCommit, vmOperands, btreeInsert, prepared, Pager.admit, Pager.phaseOne,
    issue, Program.run.eq_1, Program.run.eq_2, Program.run.eq_3, journalWrite, journalSync]
  exact ⟨trivial, trivial, rfl, rfl⟩

end Silmaril.Proofs.Machine.SqliteVfs.TrackA.Write
