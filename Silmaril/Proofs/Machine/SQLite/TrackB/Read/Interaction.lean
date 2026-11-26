module

public import Silmaril.Machine.SQLite.TrackB.Read.Thms
public import Silmaril.Machine.SQLite.TrackA.Read.Interaction.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.TrackB.Read.Interaction

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SQLite
open Silmaril.Machine.SqliteVfs
open Silmaril.Semantics
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)
open Silmaril.Machine.SQLite.TrackA.Read.Interaction (VfsSignature pagerTree pagerHandler vfsTree vfsExchanges)

local notation "finiteTrace" => Silmaril.Semantics.TrackA.Interaction.Trace.finite
open Silmaril.Machine.SQLite.TrackB.Read

/-- The supplied backing handler fixes the typed Pager reply. Its completed
VFS exchanges are retained in the returned outcome. -/
theorem handledPager_returns_run {Backing : Type} (backing : Handler Backing)
    (file : Backing) (cache : PageRead.Cache) (target : PageRead.SlotId)
    (page : PageRead.Page) (key : Int64) :
    let tree := pagerTree Backing target page key
    let handled := tree.unfold.handle (T := VfsSignature) (pagerHandler backing)
    finiteTrace [] (.returned (run backing file cache target page key)) ∈
      handled.observes (tree.root (), file, cache) := by
  simpa only [run_eq_staged] using
    TrackA.Read.Interaction.handledPager_returns_staged backing file cache target page key

/-- Among the possible observations of the open VFS tree is the finite path
using exactly the supplied handler's replies. The same exchanges validate
that handler's file transition, including ordinary acquisition errors. -/
theorem vfsTree_observes_run {Backing : Type} (backing : Handler Backing)
    (file : Backing) (cache : PageRead.Cache) (target : PageRead.SlotId)
    (page : PageRead.Page) (key : Int64) :
    let outcome := run backing file cache target page key
    let tree := vfsTree cache target page key
    Trace.Valid backing file outcome.exchanges outcome.file ∧
      finiteTrace (vfsExchanges outcome.exchanges)
        (.returned (outcome.result, outcome.cache)) ∈ tree.unfold.observes (tree.root ()) := by
  simpa only [run_eq_staged] using
    TrackA.Read.Interaction.vfsTree_corresponds backing file cache target page key

/-- On an admitted acquisition from this handler, an actual generic Page run
supplies the row projected by the interpreted typed Pager return. -/
theorem handledPager_returns_page {Backing : Type} (backing : Handler Backing)
    (file : Backing) (cache : PageRead.Cache) (target : PageRead.SlotId)
    (page : PageRead.Page) (key : Int64) {bytes : Silmaril.Machine.SqliteVfs.Bytes}
    {table : Vdbe.Table}
    (supplied : (PageRead.Acquire.acquire backing file cache target page).result = .ok bytes)
    (admitted : FileView.VdbeLeaf.table? (acquiredView bytes)
      (btreeHeaderOffset page.number) = some table) :
    let acquired := PageRead.Acquire.acquire backing file cache target page
    let memory := leafMemory page.number table
    let tree := pagerTree Backing target page key
    let handled := tree.unfold.handle (T := VfsSignature) (pagerHandler backing)
    ∃ row, Page.Run leafModel (pageLookup page.number key) memory [] (.returned row memory) ∧
      finiteTrace [] (.returned ⟨.ok (project row), acquired.file, acquired.cache, acquired.trace⟩) ∈
        handled.observes (tree.root (), file, cache) := by
  obtain ⟨row, genericRun, finished⟩ := finishAcquire_page
    (PageRead.Acquire.acquire backing file cache target page) page.number key supplied admitted
  change TrackA.Read.runStaged backing file cache target page key = _ at finished
  have observed := TrackA.Read.Interaction.handledPager_returns_staged
    backing file cache target page key
  dsimp only at observed
  rw [finished] at observed
  exact ⟨row, genericRun, observed⟩

/-- The read-only handler picks one complete cold VFS exchange and an empty
warm trace. Both typed returns project the generic run on the cached bytes. -/
theorem readOnly_cold_warm_observations (capacity : Nat) (file : FileState) (image : File.Image)
    (number : Nat) (view : File.View) (handle : Handle) (cache : PageRead.Cache)
    (target : PageRead.SlotId) (key : Int64) (table : Vdbe.Table)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false)
    (range : ReadRange ((number - 1) * image.header.pageSize : Nat) image.header.pageSize)
    (owned : cache target = some .vacant)
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table) :
    let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
    let memory := leafMemory number table
    let pager := pagerTree FileState target page key
    let handled := pager.unfold.handle (T := VfsSignature) (pagerHandler (readOnly capacity))
    let coldVfs := vfsTree cache target page key
    ∃ bytes row,
      let resident := cache.install target page bytes
      let warmVfs := vfsTree resident target page key
      let cold : TrackA.Read.Outcome FileState :=
        ⟨.ok (project row), file, resident, [⟨page.request, .ok bytes⟩]⟩
      let warm : TrackA.Read.Outcome FileState := ⟨cold.result, cold.file, cold.cache, []⟩
      FileView.VdbeLeaf.table? (acquiredView bytes) (btreeHeaderOffset number) = some table ∧
      Page.Run leafModel (pageLookup number key) memory [] (.returned row memory) ∧
      Trace.Valid (readOnly capacity) file (cold.exchanges ++ warm.exchanges) warm.file ∧
      finiteTrace [] (.returned cold) ∈ handled.observes (pager.root (), file, cache) ∧
      finiteTrace [] (.returned warm) ∈ handled.observes (pager.root (), cold.file, cold.cache) ∧
      finiteTrace (vfsExchanges cold.exchanges) (.returned (cold.result, cold.cache)) ∈
        coldVfs.unfold.observes (coldVfs.root ()) ∧
      finiteTrace (vfsExchanges warm.exchanges) (.returned (warm.result, warm.cache)) ∈
        warmVfs.unfold.observes (warmVfs.root ()) := by
  let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
  let backing := readOnly capacity
  obtain ⟨bytes, row, copied, genericRun, cold, warm, valid⟩ :=
    readOnly_cold_warm_page capacity file image number view handle cache target key table
      snapshot found live range owned admitted
  rw [cold] at warm
  rw [cold, warm] at valid
  have pagerCold := handledPager_returns_run backing file cache target page key
  have pagerWarm := handledPager_returns_run backing file
    (cache.install target page bytes) target page key
  have vfsCold := (vfsTree_observes_run backing file cache target page key).2
  have vfsWarm := (vfsTree_observes_run backing file
    (cache.install target page bytes) target page key).2
  dsimp only at pagerCold pagerWarm
  rw [cold] at pagerCold vfsCold
  rw [warm] at pagerWarm vfsWarm
  exact ⟨bytes, row, copied, genericRun, valid, pagerCold, pagerWarm, vfsCold, vfsWarm⟩

end Silmaril.Proofs.Machine.SQLite.TrackB.Read.Interaction
