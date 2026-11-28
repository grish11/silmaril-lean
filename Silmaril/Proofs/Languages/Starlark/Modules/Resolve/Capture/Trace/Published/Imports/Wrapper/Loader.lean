module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Defs
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Execution
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper.Link
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Producer
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Modules.Loader.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (enter fileSlot globalSlot validateSource)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Lists (State)
open Silmaril.Languages.Starlark.Modules.Loader (Session)

private theorem concludes (wrapper : Wrapper) {commands : List Modules.Resolve.Command}
    {producer consumer : ResolvedModule} {exports : Environment} (caller : Session)
    (checked : resolve wrapper.commands producer.program = .ok consumer)
    (sourceLinks : ∀ name callee, exports name = some callee → callee.Linked producer.program)
    (uncached : caller.cache.lookup 1 = none)
    (covered : (∃ callee, exports wrapper.imported = some callee) ∨ wrapper.imported ∉ Trace.names commands)
    {dependency : Modules.Loader.Result Modules.Published}
    (ranDependency : Producer commands producer.source {caller with runtime := enter consumer.source caller.runtime} dependency)
    (nativeDependency : Modules.Loader.Runs consumer.program (wrapper.graph producer consumer) [1] (.initialize 0)
      {caller with runtime := enter consumer.source caller.runtime} dependency)
    (slots : (reachedSession dependency).runtime.slots = (enter consumer.source caller.runtime).slots)
    (kept : KeepsContents (enter consumer.source caller.runtime) (reachedSession dependency).runtime)
    (publication : ∀ published reached, dependency = .ok published reached →
      PublishedLive exports consumer.program published reached.runtime ∧
      ∀ name value, published.exports.lookup name = some value → name ∈ Trace.names commands) :
    wrapper.Agrees producer consumer commands exports caller := by
  obtain ⟨_, code, globals, files⟩ := layout wrapper checked
  let manifest := wrapper.graph producer consumer
  have label : Modules.Loader.resolve manifest 1 wrapper.label = some 0 := by
    simp [manifest, Wrapper.graph, Modules.Loader.resolve]
  have complete (out : Modules.Loader.Result Unit)
      (ran : Modules.Loader.Runs consumer.program manifest [1] (.commands 1 (wrapper.moduleCode producer.program))
        {caller with runtime := enter consumer.source caller.runtime} out) :
      Modules.Loader.Runs consumer.program manifest [] (.initialize 1) caller
        (Modules.Loader.finish 1 consumer.source caller.runtime out) := by
    apply Modules.Loader.Runs.initialize (by simp [manifest, Wrapper.graph]) (by simp) uncached (checked_of_resolve checked).2.2.2
    change Modules.Loader.Runs consumer.program manifest [1] (.commands 1 consumer.source.commands) _ out
    rw [code]
    exact ran
  cases dependency with
  | error error reached =>
    have native := complete _ (.failed (.loadFailed label nativeDependency))
    exact ⟨_, .dependencyError ranDependency, native, (Modules.Loader.runs_iff_denote _ _ _ _ _ _).mp native⟩
  | ok published reached =>
    obtain ⟨live, declared⟩ := publication published reached rfl
    have load := Modules.Loader.Runs.load (imports := [⟨wrapper.imported, wrapper.alias⟩]) label nativeDependency
    rcases covered with ⟨callee, tracked⟩ | absent
    · obtain ⟨_, address, defining, loaded, record, _⟩ :=
        live _ callee tracked wrapper.publicImport
      have linkedOriginal := sourceLinks _ callee tracked
      have cell (binding : Binding) (member : binding ∈ consumer.source.globals.map globalSlot ++ consumer.source.fileNames.map fileSlot) :
          ∃ address frozen, reached.runtime.slots binding = some (.owned address) ∧
            reached.runtime.heap[address]? = some ⟨.binding none, frozen⟩ := by
        obtain ⟨address, slot, stored⟩ := Entry.entered_blank consumer.source caller.runtime binding member
        obtain ⟨frozen, found⟩ := kept _ _ stored
        exact ⟨address, frozen, slots ▸ slot, found⟩
      obtain ⟨aliasCell, aliasFrozen, aliasOwned, aliasStored⟩ := cell (fileSlot wrapper.alias) (by simp [globals, files])
      obtain ⟨targetCell, targetFrozen, targetOwned, targetStored⟩ := cell (globalSlot wrapper.name) (by simp [globals, files])
      have distinct : aliasCell ≠ targetCell := by
        intro same
        have equal := RootCall.enter_distinct consumer.source caller.runtime (fileSlot wrapper.alias)
          (globalSlot wrapper.name) aliasCell (slots.symm ▸ aliasOwned) (slots.symm ▸ (same ▸ targetOwned))
        cases equal
      let bound := reached.runtime.write (fileSlot wrapper.alias) (.function address)
      have boundAlias := written_cell (.function address) aliasOwned aliasStored
      have boundTarget : bound.heap[targetCell]? = some ⟨.binding none, targetFrozen⟩ :=
        (RootCall.write_other_cell reached.runtime _ _ targetCell (by simp [aliasOwned, distinct])).trans targetStored
      obtain ⟨boundRecord⟩ := write_slot_record record aliasOwned aliasStored (.function address)
      obtain ⟨out, source, nativeTail⟩ := run_bound wrapper checked linkedOriginal (state := bound) boundRecord
        (by rw [write_slots]; exact aliasOwned) boundAlias (by rw [write_slots]; exact targetOwned) boundTarget distinct manifest
      have imported : Modules.Loader.Runs consumer.program manifest [1]
          (.command 1 (.load wrapper.label [⟨wrapper.imported, wrapper.alias⟩]))
          {caller with runtime := enter consumer.source caller.runtime} (.ok () ⟨bound, reached.cache⟩) := by
        simpa [Modules.importsOf, Modules.bindImports, wrapper.publicImport, loaded, bind, Except.bind,
          pure, Except.pure, Modules.Loader.liftResult, bound] using load
      have native := complete _ (.step imported (nativeTail reached.cache))
      rw [← observed_eq (before := ⟨bound, reached.cache⟩)] at native
      exact ⟨_, .invoked ranDependency loaded tracked source, native, (Modules.Loader.runs_iff_denote _ _ _ _ _ _).mp native⟩
    · have missing : published.exports.lookup wrapper.imported = none := by
        cases found : published.exports.lookup wrapper.imported with
        | none => rfl
        | some value => exact (absent (declared _ value found)).elim
      have failed : Modules.Loader.Runs consumer.program manifest [1]
          (.command 1 (.load wrapper.label [⟨wrapper.imported, wrapper.alias⟩]))
          {caller with runtime := enter consumer.source caller.runtime}
          (Modules.Loader.liftResult 1 reached (.error (.missingExport wrapper.label wrapper.imported) reached.runtime)) := by
        simpa [Modules.importsOf, Modules.bindImports, wrapper.publicImport, missing, bind, Except.bind,
          throw, throwThe, MonadExceptOf.throw, pure, Except.pure] using load
      have native := complete _ (.failed failed)
      exact ⟨_, .missing ranDependency missing, native, (Modules.Loader.runs_iff_denote _ _ _ _ _ _).mp native⟩

theorem cold_agrees (wrapper : Wrapper) {commands : List Modules.Resolve.Command} {seed final : Program}
    {code : List Modules.Command} {producer consumer : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands seed code final exports)
    (producerChecked : resolve commands seed = .ok producer)
    (consumerChecked : resolve wrapper.commands producer.program = .ok consumer)
    (covered : (∃ callee, exports wrapper.imported = some callee) ∨ wrapper.imported ∉ Trace.names commands)
    (caller : State) :
    wrapper.Agrees producer consumer commands exports ⟨caller, []⟩ := by
  have valid := revalidate (checked_of_resolve producerChecked).2.2.2 (checked_of_resolve consumerChecked).2.2.2
  obtain ⟨_, source, native, slots, kept, ready⟩ := producer_cold_extending profile producerChecked consumerChecked
    (linked wrapper consumerChecked).1 valid (manifest := wrapper.graph producer consumer)
    (by simp [Wrapper.graph]) (by simp [Wrapper.graph]) [1] (by decide) ⟨enter consumer.source caller, []⟩ rfl
  exact concludes wrapper ⟨caller, []⟩ consumerChecked (fun _ _ tracked => plan_exports_linked profile producerChecked tracked)
    rfl covered source native slots kept (fun published reached same => (ready published reached same).2)

theorem preloaded_agrees (wrapper : Wrapper) {commands : List Modules.Resolve.Command} {seed final : Program}
    {code : List Modules.Command} {producer consumer : ResolvedModule} {exports : Environment}
    (profile : Plan (Trace.names commands) (fun _ => none) commands seed code final exports)
    (producerChecked : resolve commands seed = .ok producer)
    (consumerChecked : resolve wrapper.commands producer.program = .ok consumer)
    (covered : (∃ callee, exports wrapper.imported = some callee) ∨ wrapper.imported ∉ Trace.names commands)
    (caller : State) :
    ∃ preload, Producer commands producer.source ⟨caller, []⟩ preload ∧
      Modules.Loader.load consumer.program (wrapper.graph producer consumer) 0 ⟨caller, []⟩ = preload ∧
      ∀ published reached, preload = .ok published reached →
        reached.cache = [(0, published)] ∧ wrapper.Agrees producer consumer commands exports reached := by
  have valid := revalidate (checked_of_resolve producerChecked).2.2.2 (checked_of_resolve consumerChecked).2.2.2
  obtain ⟨out, source, native, _, _, ready⟩ := producer_cold_extending profile producerChecked consumerChecked
    (linked wrapper consumerChecked).1 valid (manifest := wrapper.graph producer consumer)
    (by simp [Wrapper.graph]) (by simp [Wrapper.graph]) [] (by decide) ⟨caller, []⟩ rfl
  refine ⟨out, source, (Modules.Loader.runs_iff_denote _ _ _ _ _ _).mp native, ?_⟩
  intro published reached successful
  obtain ⟨cache, live, declared⟩ := ready _ _ successful
  let entered := {reached with runtime := enter consumer.source reached.runtime}
  have hit : entered.cache.lookup 0 = some published := by simp [entered, cache]
  have cachedSource : Producer commands producer.source entered (.ok published entered) := .cached hit
  have cachedNative : Modules.Loader.Runs consumer.program (wrapper.graph producer consumer) [1] (.initialize 0)
      entered (.ok published entered) := .cached (by decide) hit
  refine ⟨cache, concludes wrapper reached consumerChecked (fun _ _ tracked => plan_exports_linked profile producerChecked tracked)
    (by simp [cache]) covered cachedSource cachedNative rfl (fun _ cell stored => ⟨cell.frozen, stored⟩) ?_⟩
  intro value final same
  cases same
  exact ⟨cached_publication live (Entry.entered_cells consumer.source reached.runtime).2, declared⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Wrapper
