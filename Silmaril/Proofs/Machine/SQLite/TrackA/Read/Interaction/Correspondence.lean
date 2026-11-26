module

public import Silmaril.Machine.SQLite.TrackA.Read.Interaction.Defs
import Silmaril.Machine.SQLite.TrackA.Read.Thms
import Silmaril.Machine.SqliteVfs.PageRead.Acquire.Thms
import Silmaril.Semantics.TrackA.Interaction.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.TrackA.Read.Interaction

open Silmaril.Machine.SQLite.TrackA
open Silmaril.Machine.SQLite.TrackA.Read.Interaction
open Silmaril.Machine.SqliteVfs
open Silmaril.Formats.Sqlite
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)
open Silmaril.Semantics.TrackA.Interaction (Coalgebra Node)

local notation "finiteTrace" => Silmaril.Semantics.TrackA.Interaction.Trace.finite

theorem vfsTree_corresponds {Backing : Type} (backing : Handler Backing)
    (file : Backing) (cache : PageRead.Cache) (target : PageRead.SlotId)
    (page : PageRead.Page) (key : Int64) :
    let outcome := Read.runStaged backing file cache target page key
    let tree := vfsTree cache target page key
    Trace.Valid backing file outcome.exchanges outcome.file ∧
      finiteTrace (vfsExchanges outcome.exchanges)
        (.returned (outcome.result, outcome.cache)) ∈ tree.unfold.observes (tree.root ()) := by
  dsimp only
  rw [Read.staged_eq_composed]
  refine ⟨Read.composed_trace backing file cache target page key, ?_⟩
  unfold Read.runComposed
  cases lookup : PageRead.CacheHit.lookup cache target page with
  | some bytes =>
    rw [PageRead.Acquire.acquire_hit backing file cache target page lookup]
    refine ⟨none, none, .nil _, .refl, ?_⟩
    simp [Coalgebra.EndsAt, vfsTree, lookup]
    rfl
  | none =>
    rw [PageRead.Acquire.acquire_miss backing file cache target page lookup]
    cases slot : cache target with
    | none =>
      rw [show PageRead.fill backing file cache target page =
        ⟨.error .unavailableSlot, file, cache, []⟩ by simp [PageRead.fill, slot]]
      refine ⟨none, none, .nil _, .refl, ?_⟩
      simp [Coalgebra.EndsAt, vfsTree, lookup, slot]
      rfl
    | some value =>
      cases value with
      | resident other data =>
        rw [show PageRead.fill backing file cache target page =
          ⟨.error .unavailableSlot, file, cache, []⟩ by simp [PageRead.fill, slot]]
        refine ⟨none, none, .nil _, .refl, ?_⟩
        simp [Coalgebra.EndsAt, vfsTree, lookup, slot]
        rfl
      | vacant =>
        by_cases admitted : page.Admitted
        · let reply := (backing file page.request).1
          let result := PageRead.accept page.size reply
          let after := match result with
            | .ok bytes => cache.install target page bytes
            | .error _ => cache
          rw [show PageRead.fill backing file cache target page =
            ⟨result, (backing file page.request).2, after, [⟨page.request, reply⟩]⟩ by
              simp [PageRead.fill, slot, admitted, reply, result, after]
              rfl]
          have layer : (vfsTree cache target page key).unfold none = .vis page.request some := by
            simp [vfsTree, lookup, slot, admitted]
          refine ⟨some reply, some reply, .cons ⟨none, .refl, ?_⟩ (.nil _), .refl, rfl⟩
          exact Coalgebra.Step.vis layer reply
        · rw [show PageRead.fill backing file cache target page =
            ⟨.error .invalidPage, file, cache, []⟩ by simp [PageRead.fill, slot, admitted]]
          refine ⟨none, none, .nil _, .refl, ?_⟩
          simp [Coalgebra.EndsAt, vfsTree, lookup, slot, admitted]
          rfl

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
        finiteTrace [] (.returned result) ∈ warm.unfold.observes (warm.root ()) := by
  let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
  obtain ⟨bytes, cold, warm, _⟩ := Read.readOnly_cold_warm_lookup capacity file image number
    view handle cache target key table snapshot found live range owned admitted
  rw [cold] at warm
  have coldTrace := (vfsTree_corresponds (readOnly capacity) file cache target page key).2
  rw [Read.staged_eq_composed, cold] at coldTrace
  have warmTrace := (vfsTree_corresponds (readOnly capacity) file
    (cache.install target page bytes) target page key).2
  rw [Read.staged_eq_composed, warm] at warmTrace
  exact ⟨bytes, coldTrace, warmTrace⟩

theorem handledPager_returns_staged {Backing : Type} (backing : Handler Backing)
    (file : Backing) (cache : PageRead.Cache) (target : PageRead.SlotId)
    (page : PageRead.Page) (key : Int64) :
    let tree := pagerTree Backing target page key
    let handled := tree.unfold.handle (T := VfsSignature) (pagerHandler backing)
    finiteTrace [] (.returned (Read.runStaged backing file cache target page key)) ∈
      handled.observes (tree.root (), file, cache) := by
  let tree := pagerTree Backing target page key
  let handled := tree.unfold.handle (T := VfsSignature) (pagerHandler backing)
  let acquisition := PageRead.Acquire.acquire backing file cache target page
  let after : tree.State × (Backing × PageRead.Cache) :=
    (some acquisition, acquisition.file, acquisition.cache)
  have enters : handled (tree.root (), file, cache) = .tau after := rfl
  change _ ∈ handled.observes (tree.root (), file, cache)
  rw [Coalgebra.observes_tau enters]
  refine ⟨after, after, .nil _, .refl, ?_⟩
  exact congrArg Node.ret (Read.staged_eq_composed backing file cache target page key).symm

end Silmaril.Proofs.Machine.SQLite.TrackA.Read.Interaction
