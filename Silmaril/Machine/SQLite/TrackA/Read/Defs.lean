module

public import Silmaril.Machine.SqliteVfs.FileView.Admission.VdbeLeaf.Defs
public import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.TrackA.Read

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)

/-- Point lookup followed by the VM's projection of the second column. -/
def lookupValue (table : Vdbe.Table) (key : Int64) : Option Value :=
  (table.get key.toInt).map fun row => row[1]?.getD .null

/-- The bounded read kernel on the designated root of database zero. -/
def program (root : Nat) (key : Int64) : Vdbe.Program :=
  #[.openRead 0 root 0, .int64 key 1, .seekRowid 0 5 1,
    .column 0 1 2, .resultRow 2 1, .halt 0]

inductive ReadError where
  | acquire (reason : PageRead.FillError)
  | leafRejected
  | vmFault (reason : Vdbe.Error)
  | vmExhausted
  | vmUnexpectedResult
  deriving DecidableEq

/-- `ok none` is a completed seek for an absent key. Failures have their own
channel, and VM halt codes remain local to the VM. -/
abbrev Result := Except ReadError (Option Value)

def observeVm : Vdbe.RunResult → Result
  | .fault reason _ => .error (.vmFault reason)
  | .exhausted _ => .error .vmExhausted
  | .halted state =>
      match state.halted, state.rows with
      | some 0, [] => .ok none
      | some 0, [[value]] => .ok (some value)
      | _, _ => .error .vmUnexpectedResult

/-- The staged B-tree lookup uses the decoded table's keyed interface. -/
def seekLeaf (view : File.View) (number : Nat) (key : Int64) : Result :=
  match FileView.VdbeLeaf.table? view (btreeHeaderOffset number) with
  | none => .error .leafRejected
  | some table => .ok (lookupValue table key)

/-- The composed leaf adapter runs the actual VDBE instructions. -/
def runLeaf (view : File.View) (number : Nat) (key : Int64) : Result :=
  match FileView.VdbeLeaf.run? view (btreeHeaderOffset number) 0 number (program number key) 6
      .initial with
  | none => .error .leafRejected
  | some vm => observeVm vm

structure Outcome (State : Type) where
  result : Result
  file : State
  cache : PageRead.Cache
  exchanges : Trace

/-- The page consumer sees the acquired byte view on success. The Pager's
poststate and completed exchanges are carried through on every path. -/
def finishAcquire {State : Type} (readLeaf : File.View → Result)
    (acquired : PageRead.Outcome State) : Outcome State :=
  let result := match acquired.result with
    | .error reason => .error (.acquire reason)
    | .ok bytes => readLeaf (File.View.ofBytes (Silmaril.Formats.Bytes.ofList bytes))
  ⟨result, acquired.file, acquired.cache, acquired.trace⟩

def runStaged {State : Type} (handler : Handler State) (file : State) (cache : PageRead.Cache)
    (target : PageRead.SlotId) (page : PageRead.Page) (key : Int64) : Outcome State :=
  let acquired := PageRead.Acquire.acquire handler file cache target page
  finishAcquire (fun view => seekLeaf view page.number key) acquired

def runComposed {State : Type} (handler : Handler State) (file : State) (cache : PageRead.Cache)
    (target : PageRead.SlotId) (page : PageRead.Page) (key : Int64) : Outcome State :=
  finishAcquire (fun view => runLeaf view page.number key)
    (PageRead.Acquire.acquire handler file cache target page)

end Silmaril.Machine.SQLite.TrackA.Read
