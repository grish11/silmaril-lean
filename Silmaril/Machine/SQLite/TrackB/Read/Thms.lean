module

public import Silmaril.Machine.SQLite.TrackB.Read.Defs
public import Silmaril.Machine.SQLite.TrackA.Read.Thms
public import Silmaril.Semantics.BTreePages.Thms
import Silmaril.Proofs.Machine.SQLite.TrackB.Read.Correctness

public section

namespace Silmaril.Machine.SQLite.TrackB.Read

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)

open Silmaril.Machine.SQLite
open Silmaril.Semantics

/-- The packed decoder checks signed key order, and record decoding preserves it. -/
theorem leaf_valid {view : File.View} {number : Nat} {table : Vdbe.Table}
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table) :
    (leaf table).Valid :=
  Proofs.Machine.SQLite.TrackB.Read.leaf_valid admitted

/-- Decoder admission gives the generic representation of the height-zero tree. -/
theorem leaf_represents {view : File.View} {number : Nat} {table : Vdbe.Table}
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table) :
    BTreePages.Represents leafModel.store (leafLayout number) (leaf table)
      (leafMemory number table) :=
  Proofs.Machine.SQLite.TrackB.Read.leaf_represents admitted

/-- Every generic run returns the full row or a miss, with unchanged memory
and no edits. The reverse direction supplies the actual run. -/
theorem page_lookup_run_iff {view : File.View} {number : Nat} {table : Vdbe.Table}
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table)
    (key : Int64) {edits : List (Page.Edit Nat LeafData)}
    {out : Page.Exit Nat LeafMemory (Option (List Value))} :
    Page.Run leafModel (pageLookup number key) (leafMemory number table) edits out ↔
      edits = [] ∧ out = .returned ((leaf table).lookup? key.toInt) (leafMemory number table) :=
  Proofs.Machine.SQLite.TrackB.Read.page_lookup_run_iff admitted key

/-- Signed key conversion and column projection agree with the VM table. -/
theorem leaf_lookup (table : Vdbe.Table) (key : Int64) :
    project ((leaf table).lookup? key.toInt) = TrackA.Read.lookupValue table key :=
  Proofs.Machine.SQLite.TrackB.Read.leaf_lookup table key

theorem lookupLeaf_eq_seekLeaf (view : File.View) (number : Nat) (key : Int64) :
    lookupLeaf view number key = TrackA.Read.seekLeaf view number key :=
  Proofs.Machine.SQLite.TrackB.Read.lookupLeaf_eq_seekLeaf view number key

theorem lookupLeaf_eq_runLeaf (view : File.View) (number : Nat) (key : Int64) :
    lookupLeaf view number key = TrackA.Read.runLeaf view number key :=
  (lookupLeaf_eq_seekLeaf view number key).trans (TrackA.Read.seekLeaf_eq_runLeaf view number key)

/-- Agreement is on the entire outcome, including any acquisition error,
the file and cache poststates, and all completed exchanges. -/
theorem run_eq_staged {State : Type} (handler : Handler State) (file : State) (cache : PageRead.Cache)
    (target : PageRead.SlotId) (page : PageRead.Page) (key : Int64) :
    run handler file cache target page key = TrackA.Read.runStaged handler file cache target page key :=
  Proofs.Machine.SQLite.TrackB.Read.run_eq_staged handler file cache target page key

theorem run_eq_composed {State : Type} (handler : Handler State) (file : State)
    (cache : PageRead.Cache) (target : PageRead.SlotId) (page : PageRead.Page) (key : Int64) :
    run handler file cache target page key = TrackA.Read.runComposed handler file cache target page key :=
  (run_eq_staged handler file cache target page key).trans
    (TrackA.Read.staged_eq_composed handler file cache target page key)

/-- A successful acquisition with an admitted copied leaf feeds the generic
run. Projecting its row gives the exact result of Track A's staged consumer. -/
theorem finishAcquire_page {State : Type} (acquired : PageRead.Outcome State)
    (number : Nat) (key : Int64) {bytes : Silmaril.Machine.SqliteVfs.Bytes} {table : Vdbe.Table}
    (supplied : acquired.result = .ok bytes)
    (admitted : FileView.VdbeLeaf.table? (acquiredView bytes) (btreeHeaderOffset number) =
      some table) :
    let memory := leafMemory number table
    ∃ row, Page.Run leafModel (pageLookup number key) memory [] (.returned row memory) ∧
      TrackA.Read.finishAcquire (fun view => TrackA.Read.seekLeaf view number key) acquired =
        ⟨.ok (project row), acquired.file, acquired.cache, acquired.trace⟩ :=
  Proofs.Machine.SQLite.TrackB.Read.finishAcquire_page acquired number key supplied admitted

/-- On a cold read, the generic run uses the table decoded from the very
bytes installed in the owned slot. The warm run reuses that page. -/
theorem readOnly_cold_warm_page (capacity : Nat) (file : FileState) (image : File.Image)
    (number : Nat) (view : File.View) (handle : Handle) (cache : PageRead.Cache)
    (target : PageRead.SlotId) (key : Int64) (table : Vdbe.Table)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false)
    (range : ReadRange ((number - 1) * image.header.pageSize : Nat) image.header.pageSize)
    (owned : cache target = some .vacant)
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table) :
    let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
    let cold := run (readOnly capacity) file cache target page key
    let warm := run (readOnly capacity) cold.file cold.cache target page key
    let memory := leafMemory number table
    ∃ bytes row,
      FileView.VdbeLeaf.table? (acquiredView bytes) (btreeHeaderOffset number) = some table ∧
      Page.Run leafModel (pageLookup number key) memory [] (.returned row memory) ∧
      cold = ⟨.ok (project row), file, cache.install target page bytes,
        [⟨page.request, .ok bytes⟩]⟩ ∧
      warm = ⟨cold.result, cold.file, cold.cache, []⟩ ∧
      Trace.Valid (readOnly capacity) file (cold.exchanges ++ warm.exchanges) warm.file :=
  Proofs.Machine.SQLite.TrackB.Read.readOnly_cold_warm_page capacity file image number view handle
    cache target key table snapshot found live range owned admitted

end Silmaril.Machine.SQLite.TrackB.Read
