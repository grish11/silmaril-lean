module

public import Silmaril.Machine.SQLite.TrackA.Read.Defs
import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Thms
import Silmaril.Proofs.Machine.SQLite.TrackA.Read.Correctness

public section

namespace Silmaril.Machine.SQLite.TrackA.Read

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)

/-- The fixed VM program halts successfully and emits the projected match or
no rows, according to the keyed table's lookup law. -/
theorem program_lookup (table : Vdbe.Table) (number : Nat) (key : Int64) :
    observeVm (Vdbe.run (FileView.VdbeLeaf.database table 0 number) (program number key) 6
      .initial) = .ok (lookupValue table key) :=
  Proofs.Machine.SQLite.TrackA.Read.program_lookup table number key

/-- Leaf admission gives a completed seek, with absence in the result channel. -/
theorem runLeaf_lookup (view : File.View) (number : Nat) (key : Int64) (table : Vdbe.Table)
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table) :
    runLeaf view number key = .ok (lookupValue table key) :=
  Proofs.Machine.SQLite.TrackA.Read.runLeaf_lookup view number key table admitted

theorem seekLeaf_eq_runLeaf (view : File.View) (number : Nat) (key : Int64) :
    seekLeaf view number key = runLeaf view number key :=
  Proofs.Machine.SQLite.TrackA.Read.seekLeaf_eq_runLeaf view number key

/-- The staged keyed lookup and the VDBE composition have the same result,
file and cache poststates, and completed VFS exchanges. -/
theorem staged_eq_composed {State : Type} (handler : Handler State) (file : State)
    (cache : PageRead.Cache) (target : PageRead.SlotId) (page : PageRead.Page) (key : Int64) :
    runStaged handler file cache target page key = runComposed handler file cache target page key :=
  Proofs.Machine.SQLite.TrackA.Read.staged_eq_composed handler file cache target page key

/-- The recorded exchanges account for the actual file transition. -/
theorem composed_trace {State : Type} (handler : Handler State) (file : State)
    (cache : PageRead.Cache) (target : PageRead.SlotId) (page : PageRead.Page) (key : Int64) :
    let after := runComposed handler file cache target page key
    Trace.Valid handler file after.exchanges after.file :=
  PageRead.Acquire.acquire_trace handler file cache target page

/-- A cold seek installs the complete root page and records one successful
read. Reusing the resulting file and cache yields the same seek result and
poststate with zero exchanges. -/
theorem readOnly_cold_warm_lookup (capacity : Nat) (file : FileState) (image : File.Image)
    (number : Nat) (view : File.View) (handle : Handle) (cache : PageRead.Cache)
    (target : PageRead.SlotId) (key : Int64) (table : Vdbe.Table)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false)
    (range : ReadRange ((number - 1) * image.header.pageSize : Nat) image.header.pageSize)
    (owned : cache target = some .vacant)
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table) :
    let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
    let cold := runComposed (readOnly capacity) file cache target page key
    let warm := runComposed (readOnly capacity) cold.file cold.cache target page key
    ∃ bytes,
      cold = ⟨.ok (lookupValue table key), file, cache.install target page bytes,
        [⟨page.request, .ok bytes⟩]⟩ ∧
      warm = ⟨cold.result, cold.file, cold.cache, []⟩ ∧
      Trace.Valid (readOnly capacity) file (cold.exchanges ++ warm.exchanges) warm.file :=
  Proofs.Machine.SQLite.TrackA.Read.readOnly_cold_warm_lookup capacity file image number view
    handle cache target key table snapshot found live range owned admitted

end Silmaril.Machine.SQLite.TrackA.Read
