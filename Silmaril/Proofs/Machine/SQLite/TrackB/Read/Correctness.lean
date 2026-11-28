module

public import Silmaril.Machine.SQLite.TrackB.Read.Defs
public import Silmaril.Machine.SQLite.TrackA.Read.Thms
public import Silmaril.Semantics.BTreePages.Thms
import Silmaril.Machine.SqliteVfs.FileView.TableLeaf.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Thms
import Silmaril.Machine.SqliteVfs.PageRead.CacheHit.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.TrackB.Read

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)
open Silmaril.Machine.SQLite.TrackB.Read

open Silmaril.Machine.SQLite
open Silmaril.Semantics

private theorem list_lookup (key : Int) (entries : List (Int × List Value)) :
    entries.lookup key = BTree.Abstract.lookupList key entries := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨other, row⟩
    by_cases same : other = key
    · subst other
      simp [BTree.Abstract.lookupList]
    · have different : (key == other) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
      simp [List.lookup_cons, BTree.Abstract.lookupList, same, different, ih]

private theorem cells_ordered {view : File.View} {base : Nat} {cells : List TableLeaf.Cell}
    (read : TableLeaf.read? view base = some cells) :
    cells.Pairwise (fun left right => left.key.toInt < right.key.toInt) := by
  unfold TableLeaf.read? at read
  obtain ⟨_, _, read⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨_, _, read⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨_, _, read⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨_, _, read⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨_, _, read⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨parsed, _, read⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨_, _, read⟩ := Option.bind_eq_some_iff.mp read
  obtain ⟨⟨⟩, ordered, accepted⟩ := Option.bind_eq_some_iff.mp read
  change some parsed = some cells at accepted
  cases accepted
  simpa [guard, Option.pure_def, failure] using ordered

private theorem row_key {cell : TableLeaf.Cell} {entry : Int × List Value}
    (read : TableLeaf.row? cell = some entry) : entry.1 = cell.key.toInt := by
  unfold TableLeaf.row? at read
  obtain ⟨fields, _, read⟩ := Option.bind_eq_some_iff.mp read
  split at read
  · cases read
    rfl
  · contradiction

private theorem row_keys {cells : List TableLeaf.Cell} {rows : List (Int × List Value)}
    (read : cells.mapM TableLeaf.row? = some rows) :
    rows.map Prod.fst = cells.map (fun cell => cell.key.toInt) := by
  induction cells generalizing rows with
  | nil =>
    cases read
    rfl
  | cons cell rest ih =>
    rw [List.mapM_cons] at read
    obtain ⟨entry, head, read⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨tail, decoded, read⟩ := Option.bind_eq_some_iff.mp read
    change some (entry :: tail) = some rows at read
    cases read
    simp only [List.map_cons, row_key head, ih decoded]

theorem leaf_valid {view : File.View} {number : Nat} {table : Vdbe.Table}
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table) :
    (leaf table).Valid := by
  unfold FileView.VdbeLeaf.table? at admitted
  obtain ⟨cells, read, admitted⟩ := Option.bind_eq_some_iff.mp admitted
  obtain ⟨rows, decoded, admitted⟩ := Option.bind_eq_some_iff.mp admitted
  change some (BTree.Query.ReadModel.ofList rows) = some table at admitted
  cases admitted
  refine ⟨?_, by simp [Semantics.BTree.InRange]⟩
  have ordered := cells_ordered read
  rw [← List.pairwise_map] at ordered
  rw [← row_keys decoded] at ordered
  exact List.pairwise_map.mp ordered

theorem leaf_represents {view : File.View} {number : Nat} {table : Vdbe.Table}
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table) :
    BTreePages.Represents leafModel.store (leafLayout number) (leaf table)
      (leafMemory number table) := by
  refine ⟨⟨leaf_valid admitted, ?_⟩, ?_⟩
  · intro left right leftHere rightHere _
    cases left <;> cases right
    · rfl
    · exact (rightHere rfl).elim
    · exact (leftHere rfl).elim
    · exact (leftHere rfl).elim
  · intro position data found
    cases position with
    | nil =>
      cases found
      change (if number = number then
        Page.Slot.defined (BTreePages.PageData.leaf table.entries : LeafData)
        else Page.Slot.absent) = _
      simp [leaf, BTreePages.encode]
    | cons => cases found

theorem page_lookup_run_iff {view : File.View} {number : Nat} {table : Vdbe.Table}
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table)
    (key : Int64) {edits : List (Page.Edit Nat LeafData)}
    {out : Page.Exit Nat LeafMemory (Option (List Value))} :
    Page.Run leafModel (pageLookup number key) (leafMemory number table) edits out ↔
      edits = [] ∧ out = .returned ((leaf table).lookup? key.toInt) (leafMemory number table) :=
  BTreePages.lookup_run_iff (leaf_represents admitted) key.toInt

theorem leaf_lookup (table : Vdbe.Table) (key : Int64) :
    project ((leaf table).lookup? key.toInt) = TrackA.Read.lookupValue table key := by
  change project (table.entries.lookup key.toInt) = _
  rw [TrackA.Read.lookupValue, table.get_eq, list_lookup]
  rfl

theorem lookupLeaf_eq_seekLeaf (view : File.View) (number : Nat) (key : Int64) :
    lookupLeaf view number key = TrackA.Read.seekLeaf view number key := by
  cases decoded : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) <;>
    simp [lookupLeaf, TrackA.Read.seekLeaf, decoded, leaf_lookup]

theorem run_eq_staged {State : Type} (handler : Handler State) (file : State) (cache : PageRead.Cache)
    (target : PageRead.SlotId) (page : PageRead.Page) (key : Int64) :
    run handler file cache target page key = TrackA.Read.runStaged handler file cache target page key := by
  simp [run, TrackA.Read.runStaged, lookupLeaf_eq_seekLeaf]

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
        ⟨.ok (project row), acquired.file, acquired.cache, acquired.trace⟩ := by
  let row := (leaf table).lookup? key.toInt
  refine ⟨row, (page_lookup_run_iff admitted key).2 ⟨rfl, rfl⟩, ?_⟩
  simp only [TrackA.Read.finishAcquire, supplied]
  change TrackA.Read.Outcome.mk (TrackA.Read.seekLeaf (acquiredView bytes) number key)
    acquired.file acquired.cache acquired.trace = _
  simp [TrackA.Read.seekLeaf, admitted, row, leaf_lookup]

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
      Trace.Valid (readOnly capacity) file (cold.exchanges ++ warm.exchanges) warm.file := by
  let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
  obtain ⟨bytes, filled, decoded⟩ := FileView.TableLeaf.image_page_fill_decode capacity file image
    number view handle cache target (btreeHeaderOffset number) snapshot found live range owned
  change PageRead.fill (readOnly capacity) file cache target page = _ at filled
  have copied : FileView.VdbeLeaf.table? (acquiredView bytes) (btreeHeaderOffset number) =
      some table := by
    unfold FileView.VdbeLeaf.table? at admitted ⊢
    rw [acquiredView, decoded]
    exact admitted
  have miss : PageRead.CacheHit.lookup cache target page = none := by
    simp [PageRead.CacheHit.lookup, owned]
  have coldAcquired :=
    (PageRead.Acquire.acquire_miss (readOnly capacity) file cache target page miss).trans filled
  have success : (PageRead.fill (readOnly capacity) file cache target page).result = .ok bytes :=
    congrArg PageRead.Outcome.result filled
  have hit := PageRead.CacheHit.lookup_after_success (readOnly capacity) file cache target
    page success
  rw [filled] at hit
  have warmAcquired := PageRead.Acquire.acquire_hit (readOnly capacity) file
    (cache.install target page bytes) target page hit
  obtain ⟨row, genericRun, finish⟩ := finishAcquire_page _ number key
    (congrArg PageRead.Outcome.result coldAcquired) copied
  rw [coldAcquired] at finish
  have cold : run (readOnly capacity) file cache target page key =
      ⟨.ok (project row), file, cache.install target page bytes, [⟨page.request, .ok bytes⟩]⟩ := by
    rw [run_eq_staged]
    simpa [TrackA.Read.runStaged, coldAcquired, page] using finish
  have warm : run (readOnly capacity) file (cache.install target page bytes) target page key =
      ⟨.ok (project row), file, cache.install target page bytes, []⟩ := by
    rw [run_eq_staged, TrackA.Read.runStaged, warmAcquired]
    have result := congrArg TrackA.Read.Outcome.result finish
    exact congrArg (fun result => TrackA.Read.Outcome.mk result file
      (cache.install target page bytes) []) result
  have trace := PageRead.Acquire.acquire_trace (readOnly capacity) file cache target page
  dsimp only at trace
  rw [coldAcquired] at trace
  dsimp only
  refine ⟨bytes, row, copied, genericRun, cold, ?_, ?_⟩
  · rw [cold]
    exact warm
  · rw [cold, warm]
    exact trace

end Silmaril.Proofs.Machine.SQLite.TrackB.Read
