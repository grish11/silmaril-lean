module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Edge
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Publication
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Producer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Invariant
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Modules.Loader.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (enter)
open Silmaril.Languages.Starlark.Modules.Loader (Manifest ModuleId Session)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Lists (State)


private theorem root_agrees {origin : Program} {manifest : Manifest} (graph : Graph origin manifest)
    {id : ModuleId} (bound : id < manifest.size) {active : List Nat} (permitted : id ∉ active)
    {commands : List Modules.Resolve.Command} {seed emitted : Program} {code : List Modules.Command}
    {resolved : ResolvedModule}
    (profile : Plan (Trace.names commands) (fun _ => none) commands seed code emitted (graph.exports id))
    (checked : resolve commands seed = .ok resolved)
    (prefixTable : PreservesDeclarations resolved.program origin)
    (entry : manifest[id].source = resolved.source)
    (caller : Session) (cold : caller.cache.lookup id = none)
    (cache : Cache origin manifest graph.exports caller) :
    ∃ out, TraceRun manifest id caller out ∧
      Modules.Loader.Runs graph.linked.program manifest active (.initialize id) caller out ∧
      Reached origin manifest graph.exports id caller out := by
  have extension : PreservesDeclarations resolved.program graph.linked.program :=
    fun index decl found => graph.includesOrigin index decl (prefixTable index decl found)
  obtain ⟨out, source, native, kept, live⟩ := module_runs_extending profile checked graph.checked extension
    (fun _ => none) caller.runtime
  have noLoads : ∀ command ∈ resolved.source.commands, ∃ top, command = .exec top := by
    rw [(plan_code profile checked).1]
    exact plan_executable profile
  have ran := loader_exec (manifest := manifest) (active := id :: active) (id := id) native noLoads caller.cache
  have valid := revalidate (checked_of_resolve checked).2.2.2 (checked_of_resolve graph.checked).2.2.2
  have initialized : Modules.Loader.Runs graph.linked.program manifest active (.initialize id) caller
      (observed id resolved.source caller.runtime caller.cache out) := by
    rw [observed_eq id resolved.source caller.runtime caller]
    rw [← entry] at valid ran ⊢
    exact .initialize bound permitted cold valid ran
  refine ⟨_, .root entry cold source, initialized, ?_⟩
  cases out with
  | error error residual =>
    exact ⟨rfl, rfl, rfl, kept, cache_transport cache (closure_cells_of_contents kept) rfl, fun _ _ found => found,
      fun _ _ impossible => nomatch impossible⟩
  | ok result state =>
    cases result
    have transported := cache_transport (next := ⟨Modules.restoreThread caller.runtime (Modules.publish resolved.source state).2,
      caller.cache⟩) cache (closure_cells_of_contents kept) rfl
    refine ⟨rfl, rfl, rfl, kept, cache_publish transported bound _ ?_,
      fun _ _ old => lookup_prepend_other cold old old _, ?_⟩
    · rw [entry]
      refine ⟨fun _ _ seen => exports_declared seen, fun name callee tracked publicName => ?_⟩
      obtain ⟨_, address, defining, exported, record, _⟩ := (live _ _ rfl) name callee tracked publicName
      exact ⟨linked_extends (plan_exports_linked profile checked tracked) prefixTable, address, defining, exported, ⟨record⟩⟩
    · intro value next same
      cases same
      simp

theorem agrees_active {origin : Program} {manifest : Manifest} (graph : Graph origin manifest)
    (id : ModuleId) (bound : id < manifest.size) (active : List ModuleId)
    (ordered : ∀ ancestor ∈ active, id < ancestor)
    (caller : Session) (cache : Cache origin manifest graph.exports caller) :
    ∃ out, TraceRun manifest id caller out ∧
      Modules.Loader.Runs graph.linked.program manifest active (.initialize id) caller out ∧
      Reached origin manifest graph.exports id caller out := by
  induction id using Nat.strongRecOn generalizing active caller with
  | ind id ih =>
    have permitted : id ∉ active := fun member => (Nat.lt_irrefl _ (ordered _ member))
    cases hit : caller.cache.lookup id with
    | some published =>
      exact ⟨_, .cached hit, .cached permitted hit, ⟨rfl, rfl, rfl, keeps_contents_refl _, cache, fun _ _ found => found,
        fun _ _ same => by cases same; exact hit⟩⟩
    | none =>
      cases graph.nodes id bound with
      | root profile checked prefixTable entry =>
        exact root_agrees graph bound permitted profile checked prefixTable entry caller hit cache
      | @importer seed plan resolved dep earlier checked prefixTable extension entry label demand =>
        let entered := {caller with runtime := enter resolved.source caller.runtime}
        have enteredCache : Cache origin manifest graph.exports entered :=
          cache_transport cache (closure_cells_of_contents (enter_keeps _ _)) rfl
        obtain ⟨loaded, trace, native, reached⟩ := ih dep earlier (Nat.lt_trans earlier bound) (id :: active)
          (fun ancestor member => (List.mem_cons.mp member).elim (fun same => same ▸ earlier)
            (fun rest => Nat.lt_trans earlier (ordered _ rest))) entered enteredCache
        obtain ⟨out, edge, executed, final⟩ := edge_agrees graph.checked plan checked prefixTable extension
          bound (Nat.lt_trans earlier bound) entry label demand permitted caller hit native reached
        exact ⟨out, .edge entry hit label trace edge, executed, final⟩

theorem agrees {origin : Program} {manifest : Manifest} (graph : Graph origin manifest)
    (id : ModuleId) (bound : id < manifest.size) (caller : Session)
    (cache : Cache origin manifest graph.exports caller) :
    ∃ out, TraceRun manifest id caller out ∧
      Modules.Loader.Runs graph.linked.program manifest [] (.initialize id) caller out ∧
      Modules.Loader.load graph.linked.program manifest id caller = out ∧
      Reached origin manifest graph.exports id caller out := by
  obtain ⟨out, source, native, reached⟩ := agrees_active graph id bound [] (by simp) caller cache
  exact ⟨out, source, native, (Modules.Loader.runs_iff_denote _ _ _ _ _ _).mp native, reached⟩

theorem requests {origin : Program} {manifest : Manifest} (graph : Graph origin manifest)
    (ids : List ModuleId) (bounded : ∀ id ∈ ids, id < manifest.size)
    (caller : Session) (cache : Cache origin manifest graph.exports caller) :
    ∃ next, Requests graph ids caller next ∧ Cache origin manifest graph.exports next := by
  induction ids generalizing caller with
  | nil => exact ⟨caller, .done caller, cache⟩
  | cons id rest ih =>
    obtain ⟨out, source, _, observed, kept⟩ := agrees graph id (bounded id List.mem_cons_self) caller cache
    obtain ⟨next, tail, final⟩ := ih (fun name member => bounded name (List.mem_cons_of_mem _ member))
      (resultSession out) kept.cache
    exact ⟨next, .more source observed tail, final⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
