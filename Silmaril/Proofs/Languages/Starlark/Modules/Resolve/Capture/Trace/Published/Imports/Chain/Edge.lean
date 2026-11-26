module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Publication
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Producer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Consumer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Invariant
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Suite
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Frame
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (enter fileSlot)
open Silmaril.Languages.Starlark.Modules.Loader (Manifest ModuleId Session)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Lists (State)


theorem edge_agrees {origin seed finalSeed : Program} {manifest : Manifest} {exports : ModuleId → Environment}
    {finalCommands : List Modules.Resolve.Command} {whole consumer : ResolvedModule}
    (wholeChecked : resolve finalCommands finalSeed = .ok whole)
    (plan : Consumer) (checked : resolve plan.commands seed = .ok consumer)
    (originPrefix : PreservesDeclarations origin seed) (extension : PreservesDeclarations consumer.program whole.program)
    {id dependencyId : ModuleId} (bound : id < manifest.size) (dependencyBound : dependencyId < manifest.size)
    (entry : manifest[id].source = consumer.source)
    (label : Modules.Loader.resolve manifest id plan.label = some dependencyId)
    (demand : Demand plan seed (exports dependencyId) manifest[dependencyId].source (exports id))
    {active : List Nat} (permitted : id ∉ active) (caller : Session) (cold : caller.cache.lookup id = none)
    {dependency : Modules.Loader.Result Modules.Published}
    (nativeDependency : Modules.Loader.Runs whole.program manifest (id :: active) (.initialize dependencyId)
      {caller with runtime := enter consumer.source caller.runtime} dependency)
    (reachedDependency : Reached origin manifest exports dependencyId
      {caller with runtime := enter consumer.source caller.runtime} dependency) :
    ∃ out, Edge plan seed id consumer.source caller.runtime dependency out ∧
      Modules.Loader.Runs whole.program manifest active (.initialize id) caller out ∧
      Reached origin manifest exports id caller out := by
  obtain ⟨same, code, globals, files⟩ := consumer_layout plan checked
  have valid := revalidate (checked_of_resolve checked).2.2.2 (checked_of_resolve wholeChecked).2.2.2
  have complete (out : Modules.Loader.Result Unit)
      (ran : Modules.Loader.Runs whole.program manifest (id :: active) (.commands id (plan.code seed))
        {caller with runtime := enter consumer.source caller.runtime} out) :
      Modules.Loader.Runs whole.program manifest active (.initialize id) caller
        (Modules.Loader.finish id consumer.source caller.runtime out) := by
    rw [← entry] at valid ran ⊢
    apply Modules.Loader.Runs.initialize bound permitted cold valid
    rwa [← code, ← entry] at ran
  cases dependency with
  | error error reached =>
    have ran := complete _ (.failed (.loadFailed label nativeDependency))
    exact ⟨_, .dependencyError, ran, ⟨rfl, rfl, rfl,
      keeps_contents_trans (enter_keeps _ _) reachedDependency.contents,
      cache_transport reachedDependency.cache (closure_cells_of_contents (keeps_contents_refl _)) rfl, reachedDependency.retained, fun _ _ impossible => nomatch impossible⟩⟩
  | ok published reached =>
    have cached := reachedDependency.published published reached rfl
    obtain ⟨_, publication⟩ := reachedDependency.cache dependencyId published cached
    have runImport {out : Modules.Result Unit} (independent : BindsAlias plan published reached.runtime out) :
        Modules.Loader.Runs whole.program manifest (id :: active) (.command id (.load plan.label [plan.item]))
          {caller with runtime := enter consumer.source caller.runtime} (Modules.Loader.liftResult id reached out) := by
      rw [← import_agrees independent]
      exact .load label nativeDependency
    have callerKept := keeps_contents_trans (enter_keeps consumer.source caller.runtime) reachedDependency.contents
    generalize selected : exports id = expected at demand
    cases demand with
    | missing absent =>
      have missing : published.exports.lookup plan.name = none := by
        cases found : published.exports.lookup plan.name with
        | none => rfl
        | some value => exact (absent (publication.1 _ _ found)).elim
      have independent := BindsAlias.missing (plan := plan) (state := reached.runtime) missing
      have native := complete _ (.failed (runImport independent))
      exact ⟨_, .missing independent, native, ⟨rfl, rfl, rfl, callerKept,
        cache_transport reachedDependency.cache (closure_cells_of_contents (keeps_contents_refl _)) rfl, reachedDependency.retained, fun _ _ impossible => nomatch impossible⟩⟩
    | found imported tracked admitted =>
      obtain ⟨linked, address, defining, loaded, ⟨record⟩⟩ := publication.2 _ imported tracked plan.publicName
      have frame := dependency_frame (plan := plan) globals files reachedDependency.slots reachedDependency.contents
      have fresh : FreshSlots caller.runtime.heap.size reached.runtime :=
        fresh_slots (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.entered_cells consumer.source caller.runtime).1
          reachedDependency.slots
      obtain ⟨_, _, _, owned, stored⟩ := frame.2 (fileSlot plan.alias) List.mem_cons_self
      let bound := reached.runtime.write (fileSlot plan.alias) (.function address)
      let session := {reached with runtime := bound}
      have boundKept : Body.Keeps caller.runtime.heap.size reached.runtime bound :=
        write_keeps_below owned (fresh _ _ owned) (.function address)
      have independent := BindsAlias.found (plan := plan) (state := reached.runtime) loaded
      have initialLive := initial_live (producer := origin) (program := whole.program) frame record linked
      have table : PreservesDeclarations (compileSuite seed plan.body).2 whole.program := same ▸ extension
      obtain ⟨out, tail, tailRan, tailKept, records, success⟩ := run_suite_preserving wholeChecked (manifest := manifest)
        (active := id :: active) (id := id) plan.separate plan.body seed originPrefix table admitted
        linked (by simp [initial, track]) session (writes_frame frame (fileSlot plan.alias) (.function address))
        caller.runtime.heap.size (fresh_slots fresh boundKept.1) initialLive
      have native := complete _ (.step (runImport independent) tailRan)
      rw [← observed_eq (before := session)] at native
      let residual := resultState out
      have kept := Body.keeps_trans boundKept tailKept
      have fromReached : ∀ (address : Nat) cell, caller.runtime.heap[address]? = some cell →
          ∃ flag, residual.heap[address]? = some {cell with frozen := flag} := by
        intro address cell found
        obtain ⟨flag, old⟩ := callerKept address cell found
        exact ⟨flag, kept.2 address _ (Array.getElem?_eq_some_iff.mp found).choose old⟩
      have cacheKept : KeepsClosureCells reached.runtime residual :=
        closure_cells_trans (write_closure_cells owned stored (.function address)) records
      refine ⟨_, .suite imported independent tail, native, ?_⟩
      cases out with
      | error =>
        have restored : KeepsClosureCells reached.runtime (Modules.restoreThread caller.runtime residual) :=
          ⟨cacheKept.functions, cacheKept.bindings⟩
        exact ⟨rfl, rfl, rfl, fromReached, cache_transport reachedDependency.cache restored rfl,
          reachedDependency.retained, fun _ _ impossible => nomatch impossible⟩
      | ok result state =>
        cases result
        obtain ⟨_, live⟩ := success state rfl
        have finalKept := publish_keeps consumer.source caller.runtime state
        have prior := cache_transport (next := ⟨Modules.restoreThread caller.runtime (Modules.publish consumer.source state).2,
            reached.cache⟩) reachedDependency.cache (closure_cells_trans cacheKept (closure_cells_of_contents finalKept)) rfl
        refine ⟨rfl, rfl, rfl, keeps_contents_trans fromReached finalKept,
          cache_publish prior ‹id < manifest.size› _ ?_,
          fun index value old => lookup_prepend_other cold old (reachedDependency.retained index value old) _, ?_⟩
        · rw [entry, selected]
          exact publication_from_suite globals caller.runtime live
        · intro value next same
          cases same
          simp

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
