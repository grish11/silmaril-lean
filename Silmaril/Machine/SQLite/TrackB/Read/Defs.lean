module

public import Silmaril.Machine.SQLite.TrackA.Read.Defs
public import Silmaril.Semantics.BTreePages.Defs
public import Mathlib.Data.Int.Order.Basic

@[expose] public section

namespace Silmaril.Machine.SQLite.TrackB.Read

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)

open Silmaril.Machine.SQLite
open Silmaril.Semantics

/-- Keep the full decoded rows and their signed keys in pointer order. -/
def leaf (table : Vdbe.Table) : Semantics.BTree.Tree Int (List Value) :=
  ⟨0, table.entries⟩

/-- VDBE's second-column projection, including its default for a short row. -/
def project (row : Option (List Value)) : Option Value :=
  row.map fun fields => fields[1]?.getD .null

/-- Decode at the same page-relative base as Track A, then look up in the
abstract leaf with the signed projection of the VM key. -/
def lookupLeaf (view : File.View) (number : Nat) (key : Int64) : TrackA.Read.Result :=
  match FileView.VdbeLeaf.table? view (btreeHeaderOffset number) with
  | none => .error .leafRejected
  | some table => .ok (project ((leaf table).lookup? key.toInt))

abbrev LeafData := BTreePages.PageData Int (List Value) Nat
abbrev LeafMemory := Page.MapMemory Nat LeafData

def leafModel : Page.Model Nat LeafData LeafMemory :=
  ⟨Page.mapStore _ _, fun _ _ => False⟩

/-- Only the root path is reachable. Its page ID is the SQLite page number. -/
def leafLayout (number : Nat) : BTreePages.Layout Nat := fun _ => number

/-- The slot contains exactly the rows obtained from decoding, in pointer order. -/
def leafMemory (number : Nat) (table : Vdbe.Table) : LeafMemory :=
  Page.override (fun _ => .absent) number (.defined (.leaf table.entries))

/-- Instantiate the generic numbered-page lookup at height zero. -/
def pageLookup (number : Nat) (key : Int64) : Page.Program Nat LeafData (Option (List Value)) :=
  BTreePages.lookup key.toInt 0 number

/-- Track A hands the consumer a zero-based view of the acquired bytes. -/
def acquiredView (bytes : Silmaril.Machine.SqliteVfs.Bytes) : File.View :=
  File.View.ofBytes (Silmaril.Formats.Bytes.ofList bytes)

/-- The Pager still owns acquisition. Its exact file, cache and VFS exchanges
are returned on both success and error. -/
def run {State : Type} (handler : Handler State) (file : State) (cache : PageRead.Cache)
    (target : PageRead.SlotId) (page : PageRead.Page) (key : Int64) : TrackA.Read.Outcome State :=
  TrackA.Read.finishAcquire (fun view => lookupLeaf view page.number key)
    (PageRead.Acquire.acquire handler file cache target page)

end Silmaril.Machine.SQLite.TrackB.Read
