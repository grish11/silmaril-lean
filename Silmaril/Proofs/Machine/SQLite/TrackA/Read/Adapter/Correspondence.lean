module

public import Silmaril.Machine.SQLite.TrackA.Read.Adapter.Defs
import Silmaril.Machine.SQLite.TrackA.Read.Thms
import Silmaril.Machine.SQLite.TrackA.Read.Interaction.Thms

public section

namespace Silmaril.Proofs.Machine.SQLite.TrackA.Read.Adapter

open Silmaril.Machine.SQLite.TrackA
open Silmaril.Machine.SQLite.TrackA.Read.Adapter
open Silmaril.Machine.SQLite.TrackA.Read.Interaction (VfsSignature vfsTree vfsExchanges)
open Silmaril.Machine.SqliteVfs
open Silmaril.Formats.Sqlite
open FileView.Admission.VdbeLeaf (btreeHeaderOffset)
open Silmaril.Semantics.TrackA.Interaction (Coalgebra Signature)

/-- Silent source steps leave the recording handler state alone. -/
private theorem handle_silent {Result Position Backing : Type}
    (tree : Coalgebra VfsSignature Signature.noChoice Result Position) (backing : Handler Backing)
    {start stop : Position} (path : tree.Silent start stop) (state : Recorded Backing) :
    (tree.handle (T := VfsSignature) (handleVfs backing)).Silent (start, state) (stop, state) := by
  induction path with
  | refl => exact .refl
  | tail _ edge ih =>
    rcases edge with edge | ⟨_, shape, _, _⟩
    · cases edge with
      | tau layer => exact ih.tail (.inl (.tau (by simp [Coalgebra.handle, layer])))
    · exact Empty.elim shape

/-- Each visible edge consumes the actual dependent reply and appends its
completed exchange. Replaying a valid trace preserves the backing order. -/
private theorem handle_follows {Result Position Backing : Type}
    (tree : Coalgebra VfsSignature Signature.noChoice Result Position) (backing : Handler Backing)
    {file after : Backing} {trace : Trace} (valid : Trace.Valid backing file trace after)
    {start stop : Position} (path : tree.Follows start (vfsExchanges trace) stop)
    (history : Trace) :
    (tree.handle (T := VfsSignature) (handleVfs backing)).Silent
      (start, file, history) (stop, after, history ++ trace) := by
  induction valid generalizing start stop history with
  | nil file =>
    change tree.Follows start [] stop at path
    cases path
    rw [List.append_nil]
    exact .refl
  | @cons file middle after request response trace reply _ ih =>
    change tree.Follows start (⟨request, response⟩ :: vfsExchanges trace) stop at path
    cases path with
    | cons head rest =>
      obtain ⟨front, silent, edge⟩ := head
      cases edge with
      | vis layer received =>
        rename_i resume
        have silentHandled := handle_silent tree backing silent (file, history)
        have visibleHandled : (tree.handle (T := VfsSignature) (handleVfs backing))
            (front, file, history) =
            .tau (resume response, middle, history ++ [⟨request, response⟩]) := by
          simp [Coalgebra.handle, layer, handleVfs, reply]
        have step := silentHandled.tail (.inl (Coalgebra.Step.tau visibleHandled))
        have remaining := ih rest (history ++ [⟨request, response⟩])
        simpa only [Coalgebra.Silent, List.append_assoc, List.singleton_append] using step.trans remaining

private theorem trace_append {Backing : Type} {backing : Handler Backing}
    {before middle after : Backing} {first second : Trace}
    (initial : Trace.Valid backing before first middle)
    (next : Trace.Valid backing middle second after) :
    Trace.Valid backing before (first ++ second) after := by
  induction initial with
  | nil => exact next
  | cons reply _ ih => exact .cons reply (ih next)

theorem interpretations_agree {Backing : Type} (backing : Handler Backing) (file : Backing)
    (cache : PageRead.Cache) (request : Acquire) (key : Int64) :
    let out := Read.runStaged backing file cache request.target request.page key
    let tree := vfsTree cache request.target request.page key
    Returns (pagerTree (stagedCall request key)) (handlePager backing)
        (file, cache, []) (out.file, out.cache, out.exchanges) (out.result, out.cache) ∧
      Returns tree (handleVfs backing) (file, []) (out.file, out.exchanges) (out.result, out.cache) ∧
      Trace.Valid backing file out.exchanges out.file ∧ Observes tree out := by
  let acquired := PageRead.Acquire.acquire backing file cache request.target request.page
  let reply : Acquired := ⟨acquired.result, acquired.cache⟩
  refine ⟨⟨some reply, .single (.inl (.tau rfl)), rfl⟩, ?_⟩
  obtain ⟨valid, observed⟩ :=
    Read.Interaction.vfsTree_corresponds backing file cache request.target request.page key
  refine ⟨?_, valid, observed⟩
  obtain ⟨mid, final, follows, silent, ending⟩ := observed
  let tree := vfsTree cache request.target request.page key
  let outcome := Read.runStaged backing file cache request.target request.page key
  have travelled := handle_follows tree.unfold backing valid follows []
  have finished := handle_silent tree.unfold backing silent (outcome.file, outcome.exchanges)
  refine ⟨final, travelled.trans finished, ?_⟩
  have returned : tree.unfold final = .ret (outcome.result, outcome.cache) := ending
  change (tree.unfold.handle (T := VfsSignature) (handleVfs backing))
    (final, outcome.file, outcome.exchanges) = .ret (outcome.result, outcome.cache)
  simp [Coalgebra.handle, returned]

theorem pagerTwice_agrees {Backing : Type} (backing : Handler Backing) (file : Backing)
    (cache : PageRead.Cache) (history : Trace) (request : Acquire) (key : Int64) :
    let cold := Read.runStaged backing file cache request.target request.page key
    let warm := Read.runStaged backing cold.file cold.cache request.target request.page key
    Returns (pagerTwice (stagedCall request key)) (handlePager backing) (file, cache, history)
        (warm.file, warm.cache, history ++ cold.exchanges ++ warm.exchanges)
        ((cold.result, cold.cache), (warm.result, warm.cache)) ∧
      Trace.Valid backing file (cold.exchanges ++ warm.exchanges) warm.file := by
  let cold := Read.runStaged backing file cache request.target request.page key
  let warm := Read.runStaged backing cold.file cold.cache request.target request.page key
  let tree := pagerTwice (stagedCall request key)
  let handled := tree.unfold.handle (T := VfsSignature) (handlePager backing)
  let second := TwoSeeks.second (cold.result, cold.cache)
  let done := TwoSeeks.done (cold.result, cold.cache) (warm.result, warm.cache)
  have firstStep : handled (.first, file, cache, history) =
      .tau (second, cold.file, cold.cache, history ++ cold.exchanges) := rfl
  have secondStep : handled (second, cold.file, cold.cache, history ++ cold.exchanges) =
      .tau (done, warm.file, warm.cache, history ++ cold.exchanges ++ warm.exchanges) := rfl
  refine ⟨⟨done, .tail (.single (.inl (.tau firstStep))) (.inl (.tau secondStep)), rfl⟩, ?_⟩
  apply trace_append
  · simpa only [← Read.staged_eq_composed] using
      Read.composed_trace backing file cache request.target request.page key
  · simpa only [← Read.staged_eq_composed] using
      Read.composed_trace backing cold.file cold.cache request.target request.page key

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
        Trace.Valid (readOnly capacity) file history file := by
  let page : PageRead.Page := ⟨handle, number, image.header.pageSize⟩
  let request : Acquire := ⟨target, page⟩
  obtain ⟨bytes, cold, warm, _⟩ := Read.readOnly_cold_warm_lookup capacity file image number
    view handle cache target key table snapshot found live range owned admitted
  rw [cold] at warm
  have actual := pagerTwice_agrees (readOnly capacity) file cache [] request key
  simp only [Read.staged_eq_composed] at actual
  rw [cold, warm] at actual
  exact ⟨bytes, actual⟩

end Silmaril.Proofs.Machine.SQLite.TrackA.Read.Adapter
