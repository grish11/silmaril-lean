module

public import Silmaril.Machine.SQLite.TrackA.Read.Interaction.Defs
public import Silmaril.Machine.SqliteVfs.TrackA.Write.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.VFS

open SqliteVfs

/-- Exact map key for the named-open profile. The parser admits ASCII
basenames and excludes "." and "..". Keys have no OS normalization. -/
def validPath (path : String) : Bool :=
  !path.isEmpty && path != "." && path != ".." &&
    path.toList.all fun c => c.isAlphanum || c == '_' || c == '-' || c == '.'

abbrev FileMap := String → Option FileState

structure OpenTarget where
  path : String
  mode : Mode
  deriving DecidableEq, Repr

inductive OpenError where
  | unsupportedName
  | modeEscalation
  | missingFile
  | backing (reason : Error)
  deriving DecidableEq, Repr

/-- URI opt-in accepts only file:NAME, file:NAME?mode=ro and
file:NAME?mode=rw. A plain NAME is permitted with or without opt-in.
The requested mode is an upper bound. The backing still checks its own
mode limit and whether the named file is already open. -/
def parseOpen (uri : Bool) (requested : Mode) (name : String) : Except OpenError OpenTarget := do
  let (path, mode) ←
    if uri && name.startsWith "file:" then
      match (name.drop 5).toString.splitOn "?" with
      | [path] => pure (path, requested)
      | [path, "mode=ro"] => pure (path, .readOnly)
      | [path, "mode=rw"] => pure (path, .readWrite)
      | _ => throw .unsupportedName
    else pure (name, requested)
  if !validPath path then throw .unsupportedName
  if requested == .readOnly && mode == .readWrite then throw .modeEscalation
  pure ⟨path, mode⟩

/-- The path selects a backing before interpreting the generation token.
A bare Track A Handle is scoped to that backing instance. -/
structure Opened where
  path : String
  handle : Handle
  deriving DecidableEq, Repr

def openExisting (maximum : Mode) (capacity : Nat) (uri : Bool) (requested : Mode)
    (name : String) (files : FileMap) : Except OpenError Opened × FileMap :=
  match parseOpen uri requested name with
  | .error reason => (.error reason, files)
  | .ok target =>
    match files target.path with
    | none => (.error .missingFile, files)
    | some file =>
      match SqliteVfs.backing maximum capacity file (.openFile target.mode) with
      | (.error reason, _) => (.error (.backing reason), files)
      | (.ok handle, after) =>
        (.ok ⟨target.path, handle⟩, fun path => if path = target.path then some after else files path)

/-- The file-side observation of a successful named open. -/
def Opened.Live (files : FileMap) (opened : Opened) (file : FileState) (mode : Mode) : Prop :=
  files opened.path = some file ∧ file.mode opened.handle = some mode

end Silmaril.Machine.SQLite.VFS
