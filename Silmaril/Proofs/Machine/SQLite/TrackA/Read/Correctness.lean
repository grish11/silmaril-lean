module

public import Silmaril.Machine.SQLite.TrackA.Read.Defs
import Silmaril.Machine.SqliteVfs.FileView.VdbeLeaf.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Thms
import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.TrackA.Read

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite.TrackA.Read
open Silmaril.Machine.SqliteVfs
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)

private theorem dropped_head_lookup (key : Int) (entries : List (Int × List Value)) :
    ((entries.dropWhile fun entry => entry.1 != key).head?).map Prod.snd =
      BTree.Abstract.lookupList key entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨other, row⟩
    by_cases same : other = key
    · simp [List.dropWhile, BTree.Abstract.lookupList, same]
    · have skip : (other != key) = true := by simpa using same
      simpa [List.dropWhile, BTree.Abstract.lookupList, same, skip] using ih

theorem program_lookup (table : Vdbe.Table) (number : Nat) (key : Int64) :
    observeVm (Vdbe.run (FileView.VdbeLeaf.database table 0 number) (program number key) 6
      .initial) = .ok (lookupValue table key) := by
  rw [lookupValue, table.get_eq, ← dropped_head_lookup]
  cases dropped : table.entries.dropWhile (fun entry => entry.1 != key.toInt) with
  | nil =>
    simp [program, FileView.VdbeLeaf.database, Vdbe.run, Vdbe.step, Vdbe.execute,
      Vdbe.State.initial, Vdbe.State.advance, Vdbe.State.write, Vdbe.State.setCursor,
      Vdbe.State.seekCursor, Vdbe.State.jump, dropped, observeVm]
  | cons entry rest =>
    simp [program, FileView.VdbeLeaf.database, Vdbe.run, Vdbe.step, Vdbe.execute,
      Vdbe.State.initial, Vdbe.State.advance, Vdbe.State.write, Vdbe.State.setCursor,
      Vdbe.State.seekCursor, Vdbe.State.jump, Vdbe.Cursor.current?, Vdbe.State.emit,
      dropped, observeVm]

theorem runLeaf_lookup (view : File.View) (number : Nat) (key : Int64) (table : Vdbe.Table)
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table) :
    runLeaf view number key = .ok (lookupValue table key) := by
  simpa [runLeaf, FileView.VdbeLeaf.run?, admitted] using program_lookup table number key

theorem seekLeaf_eq_runLeaf (view : File.View) (number : Nat) (key : Int64) :
    seekLeaf view number key = runLeaf view number key := by
  cases decoded : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) with
  | none => simp [seekLeaf, runLeaf, FileView.VdbeLeaf.run?, decoded]
  | some table => rw [runLeaf_lookup view number key table decoded]; simp [seekLeaf, decoded]

theorem staged_eq_composed {State : Type} (handler : Handler State) (file : State)
    (cache : PageRead.Cache) (target : PageRead.SlotId) (page : PageRead.Page) (key : Int64) :
    runStaged handler file cache target page key = runComposed handler file cache target page key := by
  simp [runStaged, runComposed, finishAcquire, seekLeaf_eq_runLeaf]

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
      Trace.Valid (readOnly capacity) file (cold.exchanges ++ warm.exchanges) warm.file := by
  let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
  obtain ⟨bytes, fill, runs⟩ := FileView.VdbeLeaf.image_page_fill_run capacity file image
    number view handle cache target (btreeHeaderOffset number) snapshot found live range owned
  change PageRead.fill (readOnly capacity) file cache target page =
    ⟨.ok bytes, file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ at fill
  have miss : PageRead.CacheHit.lookup cache target page = none := by
    simp [PageRead.CacheHit.lookup, owned]
  have coldAcquired := (PageRead.Acquire.acquire_miss (readOnly capacity) file cache target
    page miss).trans fill
  have success : (PageRead.fill (readOnly capacity) file cache target page).result = .ok bytes := by
    rw [fill]
  have hit := PageRead.CacheHit.lookup_after_success (readOnly capacity) file cache target
    page success
  rw [fill] at hit
  have warmAcquired := PageRead.Acquire.acquire_hit (readOnly capacity) file
    (cache.install target page bytes) target page hit
  have result : runLeaf (File.View.ofBytes (Silmaril.Formats.Bytes.ofList bytes)) number key =
      .ok (lookupValue table key) := by
    unfold runLeaf
    rw [runs 0 number (program number key) 6 .initial]
    exact runLeaf_lookup view number key table admitted
  have cold : runComposed (readOnly capacity) file cache target page key =
      ⟨.ok (lookupValue table key), file, cache.install target page bytes,
        [⟨page.request, .ok bytes⟩]⟩ := by
    simp [runComposed, coldAcquired, finishAcquire, page, result]
  have warm : runComposed (readOnly capacity) file (cache.install target page bytes) target page key =
      ⟨.ok (lookupValue table key), file, cache.install target page bytes, []⟩ := by
    simp [runComposed, warmAcquired, finishAcquire, page, result]
  have valid := PageRead.Acquire.acquire_trace (readOnly capacity) file cache target page
  dsimp only at valid
  rw [coldAcquired] at valid
  refine ⟨bytes, cold, ?_, ?_⟩
  · rw [cold]
    exact warm
  · rw [cold, warm]
    exact valid

end Silmaril.Proofs.Machine.SQLite.TrackA.Read
