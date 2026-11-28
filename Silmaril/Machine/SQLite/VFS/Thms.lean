module

public import Silmaril.Machine.SQLite.VFS.Defs
public import Silmaril.Machine.SqliteVfs.Thms
import Silmaril.Proofs.Machine.SQLite.VFS.Open

public section

namespace Silmaril.Machine.SQLite.VFS

open SqliteVfs

/-- The exact parsed map entry supplies the live handle, keeps its bytes and
generation, and leaves every other path unchanged. -/
theorem open_success {maximum : Mode} {capacity : Nat} {uri : Bool} {requested : Mode}
    {name : String} {files after : FileMap} {opened : Opened}
    (success : openExisting maximum capacity uri requested name files = (.ok opened, after)) :
    ∃ target file,
      parseOpen uri requested name = .ok target ∧ files target.path = some file ∧
      file.openMode = none ∧ (maximum = .readOnly → target.mode = .readOnly) ∧
      opened = ⟨target.path, ⟨file.generation⟩⟩ ∧
      opened.Live after { file with openMode := some target.mode } target.mode ∧
      ∀ path, path ≠ target.path → after path = files path :=
  Proofs.Machine.SQLite.VFS.open_success success

theorem open_error_preserves {maximum : Mode} {capacity : Nat} {uri : Bool} {requested : Mode}
    {name : String} {files after : FileMap} {reason : OpenError}
    (failure : openExisting maximum capacity uri requested name files = (.error reason, after)) :
    after = files :=
  Proofs.Machine.SQLite.VFS.open_error_preserves failure

end Silmaril.Machine.SQLite.VFS
