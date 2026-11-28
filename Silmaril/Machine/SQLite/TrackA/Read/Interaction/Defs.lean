module

public import Silmaril.Machine.SQLite.TrackA.Read.Defs
public import Silmaril.Semantics.TrackA.Interaction.Defs

@[expose] public section

namespace Silmaril.Machine.SQLite.TrackA.Read.Interaction

open Silmaril.Machine.SqliteVfs
open Silmaril.Semantics.TrackA.Interaction (Signature ITree Coalgebra)

abbrev VfsSignature : Signature := ⟨Request, Response⟩

/-- Keep the original request and its dependent reply in the tree observation. -/
def vfsExchanges (trace : Trace) : List VfsSignature.Exchange :=
  trace.map fun e => ⟨e.request, e.response⟩

/-- The VFS drives the file transition. The leaf continuation returns the
search result and the Pager's cache poststate. -/
abbrev LeafResult := Read.Result × PageRead.Cache

/-- Run the existing leaf continuation after the Pager determines the cache. -/
def finishLeaf (page : PageRead.Page) (key : Int64) (cache : PageRead.Cache)
    (result : Except PageRead.FillError Bytes) : LeafResult :=
  let outcome := Read.finishAcquire (fun view => Read.runLeaf view page.number key)
    (⟨result, (), cache, []⟩ : PageRead.Outcome Unit)
  (outcome.result, outcome.cache)

/-- Expose the target-page VFS request on a vacant, admitted miss. The reply
feeds the strict page acceptance rule and then the VM leaf continuation. -/
def vfsTree (cache : PageRead.Cache) (target : PageRead.SlotId) (page : PageRead.Page)
    (key : Int64) : ITree VfsSignature LeafResult where
  State := Option ReadReply
  root := fun _ => none
  unfold
    | some reply =>
        let result := PageRead.accept page.size reply
        let after := match result with
          | .ok bytes => cache.install target page bytes
          | .error _ => cache
        .ret (finishLeaf page key after result)
    | none =>
        match PageRead.CacheHit.lookup cache target page with
        | some bytes => .ret (finishLeaf page key cache (.ok bytes))
        | none =>
            match cache target with
            | some .vacant =>
                if page.Admitted then .vis page.request some
                else .ret (finishLeaf page key cache (.error .invalidPage))
            | _ => .ret (finishLeaf page key cache (.error .unavailableSlot))

abbrev PagerSignature (Backing : Type) : Signature :=
  ⟨PageRead.SlotId × PageRead.Page, fun _ => PageRead.Outcome Backing⟩

/-- Handle one acquisition using the chosen VFS handler and the actual Pager
operation. The outcome includes the completed target-page exchanges. -/
def pagerHandler {Backing : Type} (backing : Coalgebra.Handler VfsSignature Backing) :
    Coalgebra.Handler (PagerSignature Backing) (Backing × PageRead.Cache) :=
  fun (file, cache) (target, page) =>
    let acquired := PageRead.Acquire.acquire backing file cache target page
    (acquired, acquired.file, acquired.cache)

/-- The VM waits for the typed acquisition reply before running the leaf. -/
def pagerTree (Backing : Type) (target : PageRead.SlotId) (page : PageRead.Page)
    (key : Int64) : ITree (PagerSignature Backing) (Read.Outcome Backing) where
  State := Option (PageRead.Outcome Backing)
  root := fun _ => none
  unfold
    | none => .vis (target, page) some
    | some acquired => .ret (Read.finishAcquire (fun view => Read.runLeaf view page.number key) acquired)

end Silmaril.Machine.SQLite.TrackA.Read.Interaction
