module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (globalSlot enter)
open Silmaril.Languages.Starlark.Modules.Resolve
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Functions
open Silmaril.Languages.Starlark.Lists (State Cell Capture)
local notation "Value" => Lists.Value

abbrev Frame (globals : List String) (state : State) : Prop :=
  RootCall.DistinctOwned state ∧ ∀ name ∈ globals, ∃ address value frozen,
    state.slots (globalSlot name) = some (.owned address) ∧ state.heap[address]? = some ⟨.binding value, frozen⟩

theorem entry_frame {source : List Silmaril.Languages.Starlark.Modules.Resolve.Command} {globals : List String} {seed : Program}
    {resolved : ResolvedModule} (declared : Block.ModuleBinders source globals)
    (checked : resolve source seed = .ok resolved) (caller : State) :
    Frame globals (enter resolved.source caller) := by
  refine ⟨RootCall.enter_distinct _ _, fun name member => ?_⟩
  obtain ⟨address, slot, cell⟩ := Entry.checked_global_cell declared checked caller name member
  exact ⟨address, none, false, slot, cell⟩

private theorem keep_cell {state next : State} (kept : Body.Keeps state.heap.size state next)
    {address : Nat} {cell : Cell} (stored : state.heap[address]? = some cell) : next.heap[address]? = some cell :=
  kept.2 _ _ (Array.getElem?_eq_some_iff.mp stored).choose stored

theorem keep_frame {globals : List String} {state next : State} (frame : Frame globals state)
    (kept : Body.Keeps state.heap.size state next) : Frame globals next := by
  refine ⟨?_, fun name member => ?_⟩
  · intro a b address first second
    exact frame.1 a b address (by rw [← kept.1]; exact first) (by rw [← kept.1]; exact second)
  · obtain ⟨address, value, frozen, owned, stored⟩ := frame.2 name member
    exact ⟨address, value, frozen, kept.1 ▸ owned, keep_cell kept stored⟩

theorem keep_captures {state next : State} {captures : List Capture} (live : Body.CaptureCells state captures)
    (kept : Body.Keeps state.heap.size state next) : Body.CaptureCells next captures := by
  intro capture member
  obtain ⟨value, frozen, cell⟩ := live capture member
  exact ⟨value, frozen, keep_cell kept cell⟩

theorem keep_record {callee : Callable} {defining state next : State} {address : Nat}
    (record : ClosureAt callee.site callee.id defining state address)
    (kept : Body.Keeps state.heap.size state next) : Nonempty (ClosureAt callee.site callee.id defining next address) :=
  ⟨{record with recorded := keep_cell kept record.recorded, live := keep_captures record.live kept}⟩

theorem keep_live {globals : List String} {env : Environment} {state next : State}
    (frame : Frame globals state) (live : Live env state)
    (tracked : ∀ name root, env name = some root → name ∈ globals)
    (kept : Body.Keeps state.heap.size state next) : Live env next := by
  intro name root chosen
  obtain ⟨address, defining, loaded, ⟨record⟩⟩ := live name root chosen
  obtain ⟨slot, value, frozen, owned, stored⟩ := frame.2 name (tracked _ _ chosen)
  have loadedNext : next.bindingValue (globalSlot name) = .ok (.function address) := by
    simpa [State.bindingValue, Lists.Slot.address, kept.1, owned, stored, keep_cell kept stored] using loaded
  exact ⟨address, defining, loadedNext, keep_record record kept⟩

theorem write_slots (state : State) (binding : Binding) (value : Value) :
    (state.write binding value).slots = state.slots := by
  unfold State.write
  split <;> try rfl
  split <;> rfl

theorem write_keeps_below {state : State} {binding : Binding} {slot floor : Nat}
    (owned : state.slots binding = some (.owned slot)) (fresh : floor ≤ slot) (value : Value) :
    Body.Keeps floor state (state.write binding value) := by
  refine ⟨write_slots state binding value, fun address cell low found => ?_⟩
  refine (RootCall.write_other_cell state binding value address ?_).trans found
  intro hit
  have equal : slot = address := by simpa [owned] using hit
  omega

theorem written_cell {state : State} {binding : Binding} {address : Nat} {old : Option Value}
    {frozen : Bool} (value : Value) (owned : state.slots binding = some (.owned address))
    (stored : state.heap[address]? = some ⟨.binding old, frozen⟩) :
    (state.write binding value).heap[address]? = some ⟨.binding (some value), frozen⟩ := by
  have within := (Array.getElem?_eq_some_iff.mp stored).choose
  simp [State.write, owned, stored, Array.getElem?_setIfInBounds_self_of_lt within]

theorem write_frame {globals : List String} {name : String} {state : State} (value : Value)
    (frame : Frame globals state) (_member : name ∈ globals) : Frame globals (state.write (globalSlot name) value) := by
  refine ⟨?_, fun read global => ?_⟩
  · intro a b address first second
    exact frame.1 a b address (by simpa only [write_slots] using first) (by simpa only [write_slots] using second)
  · obtain ⟨slot, old, frozen, owned, stored⟩ := frame.2 read global
    have reached : (state.write (globalSlot name) value).slots (globalSlot read) = some (.owned slot) := by
      simpa only [write_slots] using owned
    by_cases same : name = read
    · subst read
      exact ⟨slot, some value, frozen, reached, written_cell value owned stored⟩
    · have other : state.slots (globalSlot name) ≠ some (.owned slot) := by
        intro equal
        exact same (congrArg Binding.name (frame.1 _ _ _ equal owned))
      exact ⟨slot, old, frozen, reached, (RootCall.write_other_cell state _ _ _ other).trans stored⟩

theorem written_binding {globals : List String} {state : State} {name : String}
    (frame : Frame globals state) (member : name ∈ globals) (value : Value) :
    (state.write (globalSlot name) value).bindingValue (globalSlot name) = .ok value := by
  obtain ⟨address, old, frozen, owned, stored⟩ := frame.2 name member
  simp [State.bindingValue, Lists.Slot.address, write_slots, owned, written_cell value owned stored]

private theorem write_captures {state : State} {captures : List Capture}
    (live : Body.CaptureCells state captures) (binding : Binding) (value : Value) :
    Body.CaptureCells (state.write binding value) captures := by
  intro capture member
  obtain ⟨old, frozen, stored⟩ := live capture member
  by_cases hit : state.slots binding = some (.owned capture.address)
  · exact ⟨some value, frozen, written_cell value hit stored⟩
  · exact ⟨old, frozen, (RootCall.write_other_cell state binding value _ hit).trans stored⟩

theorem write_slot_record {callee : Callable} {defining state : State} {address slot : Nat}
    {target : Binding} {old : Option Value} {frozen : Bool}
    (record : ClosureAt callee.site callee.id defining state address)
    (owned : state.slots target = some (.owned slot))
    (stored : state.heap[slot]? = some ⟨.binding old, frozen⟩) (value : Value) :
    Nonempty (ClosureAt callee.site callee.id defining (state.write target value) address) := by
  have other : state.slots target ≠ some (.owned address) := by
    intro hit
    have equal : slot = address := by simpa [owned] using hit
    subst slot
    rw [record.recorded] at stored
    cases stored
  exact ⟨{record with
    recorded := (RootCall.write_other_cell state _ _ _ other).trans record.recorded
    live := write_captures record.live _ _}⟩

theorem write_record {globals : List String} {root : Callable} {defining state : State}
    {address : Nat} (record : ClosureAt root.site root.id defining state address)
    (frame : Frame globals state) {name : String} (member : name ∈ globals) (value : Value) :
    Nonempty (ClosureAt root.site root.id defining (state.write (globalSlot name) value) address) := by
  obtain ⟨slot, old, frozen, owned, stored⟩ := frame.2 name member
  exact write_slot_record record owned stored value

theorem write_live {globals : List String} {state : State} {env : Environment}
    (frame : Frame globals state) (live : Live env state)
    (tracked : ∀ name root, env name = some root → name ∈ globals)
    {name : String} (member : name ∈ globals) (value : Value) (updated : Option Callable)
    (new : ∀ root, updated = some root → ∃ address defining, value = .function address ∧
      Nonempty (ClosureAt root.site root.id defining state address)) :
    Live (update env name updated) (state.write (globalSlot name) value) := by
  intro read root found
  by_cases same : read = name
  · subst read
    obtain ⟨address, defining, rfl, ⟨record⟩⟩ := new root (by simpa [update] using found)
    exact ⟨address, defining, written_binding frame member _, write_record record frame member _⟩
  · have seen : env read = some root := by simpa [update, same] using found
    obtain ⟨address, defining, loaded, ⟨record⟩⟩ := live read root seen
    obtain ⟨slot, _, _, owned, _⟩ := frame.2 read (tracked _ _ seen)
    have retained := RootCall.write_keeps_live state read name value
      (id := root.id) (captures := record.captures) (defaults := root.site.defaultKeys.zip record.defaults)
      frame.1 ⟨⟨slot, owned⟩, loaded, record.recorded⟩ (Ne.symm same)
    exact ⟨address, defining, retained.2.binding, write_record record frame member _⟩

theorem root_captures {globals : List String} (root : Root globals) {state : State}
    (frame : Frame globals state) :
    ∃ captures, Installs state root.site.free captures ∧ Body.CaptureCells state captures := by
  have source (entry : FreeName) (member : entry ∈ root.site.free) :
      ∃ name, name ∈ globals ∧ entry = ⟨globalSlot name, globalSlot name⟩ := by
    obtain ⟨binding, rfl, origin | origin⟩ := selected_origin root.site.selects entry member
    · cases origin with
      | enclosing _ outside => simp [moduleLex] at outside
    · cases origin with
      | module _ _ global => exact ⟨_, global, rfl⟩
  generalize root.site.free = free at source
  induction free with
  | nil => exact ⟨[], .nil, fun _ h => nomatch h⟩
  | cons first rest ih =>
    obtain ⟨name, declared, rfl⟩ := source first List.mem_cons_self
    obtain ⟨address, value, frozen, owned, stored⟩ := frame.2 name declared
    obtain ⟨tail, installed, live⟩ := ih fun entry member => source entry (List.mem_cons_of_mem _ member)
    refine ⟨_, .cons (.ownedGlobal owned) installed, ?_⟩
    intro capture member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨value, frozen, stored⟩
    · exact live capture later

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
