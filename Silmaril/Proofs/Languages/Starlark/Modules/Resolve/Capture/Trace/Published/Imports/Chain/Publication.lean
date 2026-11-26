module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Lists.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Producer
import Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Invariant

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (globalSlot)
open Silmaril.Languages.Starlark.Modules.Loader (Manifest ModuleId Session)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
open Silmaril.Languages.Starlark.Lists (State)
open Silmaril.Languages.Starlark.Functions (Program)

theorem keeps_contents_refl (state : State) : KeepsContents state state :=
  fun _ cell stored => ⟨cell.frozen, stored⟩

theorem keeps_contents_trans {first middle last : State}
    (one : KeepsContents first middle) (two : KeepsContents middle last) : KeepsContents first last := by
  intro address cell stored
  obtain ⟨flag, middleStored⟩ := one address cell stored
  obtain ⟨next, lastStored⟩ := two address {cell with frozen := flag} middleStored
  exact ⟨next, lastStored⟩

theorem keeps_publication {exports : Environment} {origin : Program} {source : Modules.Source}
    {published : Modules.Published} {state next : State}
    (live : Publication exports origin source published state) (kept : KeepsClosureCells state next) :
    Publication exports origin source published next := by
  refine ⟨live.1, fun name callee tracked publicName => ?_⟩
  obtain ⟨linked, address, defining, loaded, ⟨record⟩⟩ := live.2 name callee tracked publicName
  obtain ⟨flag, present⟩ := kept.functions _ _ _ record.recorded
  refine ⟨linked, address, defining, loaded, ⟨{ record with frozen := flag, recorded := present, live := ?_ }⟩⟩
  intro capture member
  obtain ⟨value, _, found⟩ := record.live capture member
  exact kept.bindings _ _ _ found

theorem publication_from_suite {plan : Consumer} {seed origin final : Program} {imported : Callable}
    {source : Modules.Source} (names : source.globals = plan.globals) (caller : State) {state : State}
    (live : Live plan.alias origin final (trackSuite imported seed (initial plan.alias imported) plan.body) state) :
    Publication (exportsOf plan seed imported) origin source (Modules.publish source state).1
      (Modules.restoreThread caller (Modules.publish source state).2) := by
  refine ⟨fun _ _ seen => exports_declared seen, fun name callee tracked publicName => ?_⟩
  unfold exportsOf at tracked
  split at tracked
  · rename_i member
    generalize found : trackSuite imported seed (initial plan.alias imported) plan.body name = entry at tracked
    cases entry with
    | none => cases tracked
    | some entry =>
      cases entry with
      | wrapper => cases tracked
      | regular selected =>
        cases tracked
        obtain ⟨address, defining, loaded, linked, ⟨record⟩, _⟩ := read_live live found
        have outside : name ≠ plan.alias := fun same => plan.separate (same ▸ member)
        have global : state.bindingValue (globalSlot name) = .ok (.function address) := by
          simpa [readSlot, outside] using loaded
        obtain ⟨exported, published, _⟩ := publish_record caller (names.symm ▸ member) publicName global record
        exact ⟨linked, address, defining, exported, ⟨published⟩⟩
  · cases tracked

theorem enter_keeps (source : Modules.Source) (state : State) : KeepsContents state (Modules.enter source state) :=
  fun address cell stored => ⟨cell.frozen,
    (Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.entered_cells source state).2 address cell stored⟩

theorem publish_keeps (source : Modules.Source) (caller state : State) :
    KeepsContents state (Modules.restoreThread caller (Modules.publish source state).2) := by
  have frozen := (Lists.freezes_iff_freeze state.heap
    (((Modules.globalValues source state).map Prod.snd).filterMap Lists.Value.address?) _).mpr rfl
  intro address cell found
  obtain ⟨flag, stored, _⟩ := frozen.cell address cell found
  exact ⟨flag, stored⟩

theorem cache_transport {origin : Program} {manifest : Manifest} {exports : ModuleId → Environment}
    {state next : Session} (valid : Cache origin manifest exports state) (kept : KeepsClosureCells state.runtime next.runtime)
    (sameCache : next.cache = state.cache) :
    Cache origin manifest exports next := by
  intro id published found
  obtain ⟨bound, live⟩ := valid id published (sameCache ▸ found)
  exact ⟨bound, keeps_publication live kept⟩

theorem lookup_prepend_other {before after : List (ModuleId × Modules.Published)}
    {id index : ModuleId} {value : Modules.Published} (cold : before.lookup id = none)
    (old : before.lookup index = some value) (retained : after.lookup index = some value)
    (published : Modules.Published) :
    ((id, published) :: after).lookup index = some value := by
  have different : (index == id) = false := by
    apply beq_eq_false_iff_ne.mpr
    intro same
    subst index
    rw [cold] at old
    cases old
  simpa [List.lookup, different] using retained

theorem cache_publish {origin : Program} {manifest : Manifest} {exports : ModuleId → Environment}
    {state : Session} (valid : Cache origin manifest exports state) {id : ModuleId} (bound : id < manifest.size)
    (published : Modules.Published)
    (live : Publication (exports id) origin manifest[id].source published state.runtime) :
    Cache origin manifest exports {state with cache := (id, published) :: state.cache} := by
  intro index value found
  by_cases same : index = id
  · subst index
    have equal : published = value := by simpa using found
    subst value
    exact ⟨bound, live⟩
  · have different : (index == id) = false := by simpa using same
    exact valid index value (by simpa [List.lookup, different] using found)

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Chain
