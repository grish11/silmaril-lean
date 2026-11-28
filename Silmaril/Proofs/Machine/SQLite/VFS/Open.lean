module

public import Silmaril.Machine.SQLite.VFS.Defs

public section

namespace Silmaril.Proofs.Machine.SQLite.VFS

open Silmaril.Machine.SqliteVfs
open Silmaril.Machine.SQLite.VFS

theorem open_success {maximum : Mode} {capacity : Nat} {uri : Bool} {requested : Mode}
    {name : String} {files after : FileMap} {opened : Opened}
    (success : openExisting maximum capacity uri requested name files = (.ok opened, after)) :
    ∃ target file,
      parseOpen uri requested name = .ok target ∧ files target.path = some file ∧
      file.openMode = none ∧ (maximum = .readOnly → target.mode = .readOnly) ∧
      opened = ⟨target.path, ⟨file.generation⟩⟩ ∧
      opened.Live after { file with openMode := some target.mode } target.mode ∧
      ∀ path, path ≠ target.path → after path = files path := by
  unfold openExisting at success
  split at success
  · cases success
  next target parsed =>
    split at success
    · cases success
    next file found =>
      by_cases rejected : file.openMode.isSome ∨ (maximum = .readOnly ∧ target.mode = .readWrite)
      · simp [Silmaril.Machine.SqliteVfs.backing, rejected] at success
      · simp [Silmaril.Machine.SqliteVfs.backing, rejected] at success
        obtain ⟨rfl, rfl⟩ := success
        refine ⟨target, file, parsed, found, ?_, ?_, rfl, ?_, ?_⟩
        · cases mode : file.openMode <;> simp_all
        · intro limit
          cases mode : target.mode <;> simp_all
        · simp [Opened.Live, FileState.mode]
        · intro path different
          simp [different]

theorem open_error_preserves {maximum : Mode} {capacity : Nat} {uri : Bool} {requested : Mode}
    {name : String} {files after : FileMap} {reason : OpenError}
    (failure : openExisting maximum capacity uri requested name files = (.error reason, after)) :
    after = files := by
  unfold openExisting at failure
  split at failure
  · exact (Prod.mk.inj failure).2.symm
  · split at failure
    · exact (Prod.mk.inj failure).2.symm
    · split at failure
      · exact (Prod.mk.inj failure).2.symm
      · cases failure

end Silmaril.Proofs.Machine.SQLite.VFS
