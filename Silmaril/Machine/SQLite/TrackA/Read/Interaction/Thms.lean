module

public import Silmaril.Machine.SQLite.TrackA.Read.Interaction.Defs
import Silmaril.Proofs.Machine.SQLite.TrackA.Read.Interaction.Correspondence

public section

namespace Silmaril.Machine.SQLite.TrackA.Read.Interaction

open Silmaril.Machine.SqliteVfs
open Silmaril.Formats.Sqlite
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)

local notation "finiteTrace" => Silmaril.Semantics.TrackA.Interaction.Trace.finite

/-- The staged file transition validates the completed exchanges. The open
VFS tree observes exactly those exchanges on the path driven by their replies
and returns the staged result and cache. -/
theorem vfsTree_corresponds {Backing : Type} (backing : Handler Backing)
    (file : Backing) (cache : PageRead.Cache) (target : PageRead.SlotId)
    (page : PageRead.Page) (key : Int64) :
    let outcome := Read.runStaged backing file cache target page key
    let tree := vfsTree cache target page key
    Trace.Valid backing file outcome.exchanges outcome.file ∧
      finiteTrace (vfsExchanges outcome.exchanges)
        (.returned (outcome.result, outcome.cache)) ∈ tree.unfold.observes (tree.root ()) :=
  Proofs.Machine.SQLite.TrackA.Read.Interaction.vfsTree_corresponds backing file cache target page key

/-- Cold and warm target-page observations return the same logical lookup.
The warm tree starts with the slot installed by the cold read. -/
theorem vfsTree_readOnly_cold_warm (capacity : Nat) (file : FileState) (image : File.Image)
    (number : Nat) (view : File.View) (handle : Handle) (cache : PageRead.Cache)
    (target : PageRead.SlotId) (key : Int64) (table : Vdbe.Table)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false)
    (range : ReadRange ((number - 1) * image.header.pageSize : Nat) image.header.pageSize)
    (owned : cache target = some .vacant)
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table) :
    let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
    let cold := vfsTree cache target page key
    ∃ bytes,
      let resident := cache.install target page bytes
      let warm := vfsTree resident target page key
      let result : LeafResult := (.ok (Read.lookupValue table key), resident)
      finiteTrace [⟨page.request, ReadReply.ok bytes⟩] (.returned result) ∈ cold.unfold.observes (cold.root ()) ∧
        finiteTrace [] (.returned result) ∈ warm.unfold.observes (warm.root ()) :=
  Proofs.Machine.SQLite.TrackA.Read.Interaction.vfsTree_readOnly_cold_warm capacity file image number
    view handle cache target key table snapshot found live range owned admitted

/-- Handling the Pager request yields the full staged outcome. The completed
VFS exchanges are in the return value across this administrative step. -/
theorem handledPager_returns_staged {Backing : Type} (backing : Handler Backing)
    (file : Backing) (cache : PageRead.Cache) (target : PageRead.SlotId)
    (page : PageRead.Page) (key : Int64) :
    let tree := pagerTree Backing target page key
    let handled := tree.unfold.handle (T := VfsSignature) (pagerHandler backing)
    finiteTrace [] (.returned (Read.runStaged backing file cache target page key)) ∈
      handled.observes (tree.root (), file, cache) :=
  Proofs.Machine.SQLite.TrackA.Read.Interaction.handledPager_returns_staged backing file cache target page key

end Silmaril.Machine.SQLite.TrackA.Read.Interaction
