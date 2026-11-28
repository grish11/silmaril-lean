module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Prefix
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Publication
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Producer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Consumer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Invariant
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Suite
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Body.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (enter fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Loader (Manifest ModuleId Session)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence (PreservesDeclarations)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
open Silmaril.Languages.Starlark.Functions (Program)

theorem ordered_agrees {origin seed finalSeed : Program} {manifest : Manifest} {exports : ModuleId → Tracked}
    {finalCommands : List Modules.Resolve.Command} {whole consumer : ResolvedModule}
    (wholeChecked : resolve finalCommands finalSeed = .ok whole)
    (plan : OrderedConsumer) (checked : resolve plan.commands seed = .ok consumer)
    (originPrefix : PreservesDeclarations origin seed) (extension : PreservesDeclarations consumer.program whole.program)
    {id : ModuleId} (bound : id < manifest.size) (entry : manifest[id].source = consumer.source)
    {finalEnv : Option Tracked}
    (imports : ImportPlan manifest exports id bound plan.imports (fun _ => none) finalEnv)
    (ready : OrderedReady plan seed finalEnv (exports id))
    {active : List ModuleId} (permitted : id ∉ active) (caller : Session) (cold : caller.cache.lookup id = none)
    (cache : Cache origin whole.program manifest exports caller)
    (loadEarlier : ∀ dependency, dependency < id → ∀ session,
      Cache origin whole.program manifest exports session →
      ∃ out, TraceRun manifest dependency session out ∧
        Modules.Loader.Runs whole.program manifest (id :: active) (.initialize dependency) session out ∧
        Reached origin whole.program manifest exports dependency session out) :
    ∃ out, TraceRun manifest id caller out ∧
      Modules.Loader.Runs whole.program manifest active (.initialize id) caller out ∧
      Reached origin whole.program manifest exports id caller out := by
  obtain ⟨same, code, globals, files⟩ := ordered_layout plan checked
  let entered := {caller with runtime := enter consumer.source caller.runtime}
  have enteredCache := cache_transport (next := entered) cache (closure_cells_of_contents (enter_keeps _ _)) rfl
  have validated := (checked_of_resolve checked).2.2.2
  have valid := revalidate validated (checked_of_resolve wholeChecked).2.2.2
  have layout := Entry.validated_entry_names validated
  rw [globals, files] at layout
  obtain ⟨globalUnique, aliasUnique, separate⟩ := List.pairwise_append.mp layout
  have reserved : ∀ binding ∈ plan.globals.map globalSlot, Blank entered.runtime binding := by
    intro binding member
    apply entered_blank_after_dependency rfl (keeps_contents_refl _)
    rw [globals]
    exact List.mem_append.mpr (.inl member)
  have frame := entry_frame globals files (state := entered.runtime) rfl (keeps_contents_refl _)
  obtain ⟨prefixOut, sourcePrefix, nativePrefix, reached⟩ := run_prefix loadEarlier imports
    (fun _ member => member) aliasUnique
    (by
      intro aliasName _ member
      obtain ⟨name, _, equal⟩ := List.mem_map.mp member
      cases equal)
    entered enteredCache frame (Entry.entered_cells consumer.source caller.runtime).1
    (fun _ _ impossible => nomatch impossible)
    (fun name member => entered_blank_after_dependency rfl (keeps_contents_refl _) (by
      rw [files]
      exact List.mem_append.mpr (.inr (List.mem_map_of_mem member))))
    reserved
  have complete (out : Modules.Loader.Result Unit)
      (ran : Modules.Loader.Runs whole.program manifest (id :: active) (.commands id (plan.code seed)) entered out) :
      Modules.Loader.Runs whole.program manifest active (.initialize id) caller
        (Modules.Loader.finish id consumer.source caller.runtime out) := by
    rw [← entry] at valid ⊢
    apply Modules.Loader.Runs.initialize bound permitted cold valid
    simpa only [entry, code] using ran
  have retainedOld (address : Nat) cell (found : caller.runtime.heap[address]? = some cell) :
      ∃ flag, (resultSession prefixOut).runtime.heap[address]? = some {cell with frozen := flag} :=
    reached.contents address cell (Array.getElem?_eq_some_iff.mp found).choose
      ((Entry.entered_cells consumer.source caller.runtime).2 address cell found)
  cases prefixOut with
  | error error stopped =>
    have ran := complete _ (nativePrefix (compileSuite seed plan.body).1 _ rfl)
    exact ⟨_, .orderedError (plan := plan) entry cold sourcePrefix, ran, ⟨rfl, rfl, rfl, retainedOld,
      cache_transport reached.cache (closure_cells_of_contents (keeps_contents_refl stopped.runtime)) rfl,
      reached.retained, fun _ _ impossible => nomatch impossible⟩⟩
  | ok result session =>
    cases result
    obtain ⟨env, someEnv, frame, live, blank⟩ := reached.ready session rfl
    rw [someEnv] at ready
    obtain ⟨admitted, publishedEnv⟩ := ready
    have outside : ∀ name ∈ plan.globals, name ∉ plan.aliases :=
      fun name member conflict => separate name member name conflict rfl
    have table : PreservesDeclarations (compileSuite seed plan.body).2 whole.program := same ▸ extension
    have fresh : FreshSlots caller.runtime.heap.size session.runtime :=
      fresh_slots (Entry.entered_cells consumer.source caller.runtime).1 reached.slots
    rw [← plan.declared] at globalUnique
    obtain ⟨out, sourceTail, nativeTail, tailKept, records, success⟩ := run_suite_preserving wholeChecked
      (manifest := manifest) (active := id :: active) (id := id) outside plan.body seed originPrefix table admitted
      globalUnique session frame (by
        intro step member
        apply blank _ (List.mem_map_of_mem _)
        exact Eq.mp (congrArg (fun names => step.destination ∈ names) plan.declared)
          (List.mem_map_of_mem (f := Step.destination) member))
      caller.runtime.heap.size fresh live
    have native := complete _ (nativePrefix _ _ nativeTail)
    rw [← observed_eq (before := session)] at native
    have fromCaller : KeepsContents caller.runtime (resultState out) := by
      intro address cell found
      obtain ⟨flag, stored⟩ := retainedOld address cell found
      exact ⟨flag, tailKept.2 address _ (Array.getElem?_eq_some_iff.mp found).choose stored⟩
    refine ⟨_, .orderedSuite (plan := plan) entry cold sourcePrefix sourceTail, native, ?_⟩
    cases out with
    | error _ stopped =>
      have restored : KeepsClosureCells session.runtime (Modules.restoreThread caller.runtime stopped) :=
        ⟨records.functions, records.bindings⟩
      exact ⟨rfl, rfl, rfl, fromCaller, cache_transport reached.cache restored rfl,
        reached.retained, fun _ _ impossible => nomatch impossible⟩
    | ok result state =>
      cases result
      obtain ⟨_, finalLive⟩ := success state rfl
      have frozen := publish_keeps consumer.source caller.runtime state
      have prior := cache_transport
        (next := ⟨Modules.restoreThread caller.runtime (Modules.publish consumer.source state).2, session.cache⟩)
        reached.cache (closure_cells_trans records (closure_cells_of_contents frozen)) rfl
      refine ⟨rfl, rfl, rfl, keeps_contents_trans fromCaller frozen, cache_publish prior bound _ ?_,
        fun index value old => lookup_prepend_other cold old (reached.retained index value old) _, ?_⟩
      · rw [entry, publishedEnv]
        exact publication_for_env globals outside caller.runtime finalLive
      · intro value next same
        cases same
        simp

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
