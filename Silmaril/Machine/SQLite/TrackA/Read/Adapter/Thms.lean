module

public import Silmaril.Machine.SQLite.TrackA.Read.Adapter.Defs
import Silmaril.Proofs.Machine.SQLite.TrackA.Read.Adapter.Correspondence

public section

namespace Silmaril.Machine.SQLite.TrackA.Read.Adapter

open Silmaril.Formats.Sqlite
open Silmaril.Machine.SqliteVfs
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)
open Read.Interaction (vfsTree)

/-- The staged Pager and composed VFS handlers reach the same one-call
result, cache, file and completed exchanges. The open VFS observation
uses the replies supplied by the backing handler. -/
theorem interpretations_agree {Backing : Type} (backing : Handler Backing) (file : Backing)
    (cache : PageRead.Cache) (request : Acquire) (key : Int64) :
    let out := Read.runStaged backing file cache request.target request.page key
    let tree := vfsTree cache request.target request.page key
    Returns (pagerTree (stagedCall request key)) (handlePager backing)
        (file, cache, []) (out.file, out.cache, out.exchanges) (out.result, out.cache) ∧
      Returns tree (handleVfs backing) (file, []) (out.file, out.exchanges) (out.result, out.cache) ∧
      Trace.Valid backing file out.exchanges out.file ∧ Observes tree out :=
  Proofs.Machine.SQLite.TrackA.Read.Adapter.interpretations_agree backing file cache request key

/-- A single handler runs two successive same-page calls. The second uses
the actual file and cache from the first, and the exchange suffix validates
that ordered file transition. -/
theorem pagerTwice_agrees {Backing : Type} (backing : Handler Backing) (file : Backing)
    (cache : PageRead.Cache) (history : Trace) (request : Acquire) (key : Int64) :
    let cold := Read.runStaged backing file cache request.target request.page key
    let warm := Read.runStaged backing cold.file cold.cache request.target request.page key
    Returns (pagerTwice (stagedCall request key)) (handlePager backing) (file, cache, history)
        (warm.file, warm.cache, history ++ cold.exchanges ++ warm.exchanges)
        ((cold.result, cold.cache), (warm.result, warm.cache)) ∧
      Trace.Valid backing file (cold.exchanges ++ warm.exchanges) warm.file :=
  Proofs.Machine.SQLite.TrackA.Read.Adapter.pagerTwice_agrees backing file cache history request key

/-- With a vacant owned slot and an admitted full leaf, both calls return
the same lookup. Starting from empty history, the handler records just the
single complete cold read. -/
theorem pagerTwice_readOnly_cold_warm (capacity : Nat) (file : FileState) (image : File.Image)
    (number : Nat) (view : File.View) (handle : Handle) (cache : PageRead.Cache)
    (target : PageRead.SlotId) (key : Int64) (table : Vdbe.Table)
    (snapshot : file.bytes = image.source.toList) (found : image.page? number = some view)
    (live : (file.mode handle).isNone = false)
    (range : ReadRange ((number - 1) * image.header.pageSize : Nat) image.header.pageSize)
    (owned : cache target = some .vacant)
    (admitted : FileView.VdbeLeaf.table? view (btreeHeaderOffset number) = some table) :
    let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
    let request : Acquire := ⟨target, page⟩
    ∃ bytes,
      let resident := cache.install target page bytes
      let history : Trace := [⟨page.request, .ok bytes⟩]
      let result : LeafResult := (.ok (Read.lookupValue table key), resident)
      Returns (pagerTwice (stagedCall request key)) (handlePager (readOnly capacity))
          (file, cache, []) (file, resident, history) (result, result) ∧
        Trace.Valid (readOnly capacity) file history file :=
  Proofs.Machine.SQLite.TrackA.Read.Adapter.pagerTwice_readOnly_cold_warm capacity file image number
    view handle cache target key table snapshot found live range owned admitted

end Silmaril.Machine.SQLite.TrackA.Read.Adapter
