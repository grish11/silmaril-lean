module

public import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports.Defs
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.Entry.Thms
import Silmaril.Languages.Starlark.Modules.Resolve.Capture.RootCall.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports

open Silmaril.Languages.Starlark
open Silmaril.Languages.Starlark.Modules (enter fileSlot globalSlot)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Defaults.Nested.Sequence.Recursive.Call (ClosureAt)
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published
open Silmaril.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
open Silmaril.Languages.Starlark.Functions (Program)
open Silmaril.Languages.Starlark.Lists (State Slot Cell)

theorem entry_frame {aliases globals : List String} {source : Modules.Source} {caller state : State}
    (names : source.globals = globals) (files : source.fileNames = aliases)
    (slots : state.slots = (enter source caller).slots) (kept : KeepsContents (enter source caller) state) :
    Frame aliases globals state := by
  refine ⟨?_, fun binding marked => ?_⟩
  · intro first second address atFirst atSecond
    exact RootCall.enter_distinct source caller first second address (slots.symm ▸ atFirst) (slots.symm ▸ atSecond)
  · have member : binding ∈ source.globals.map globalSlot ++ source.fileNames.map fileSlot := by
      rw [names, files]
      simpa [List.mem_append, or_comm] using marked
    obtain ⟨address, owned, blank⟩ := Entry.entered_blank source caller binding member
    obtain ⟨frozen, found⟩ := kept _ _ blank
    exact ⟨address, none, frozen, slots ▸ owned, found⟩

theorem dependency_frame {plan : Consumer} {source : Modules.Source} {caller state : State}
    (globals : source.globals = plan.globals) (files : source.fileNames = [plan.alias])
    (slots : state.slots = (enter source caller).slots) (kept : KeepsContents (enter source caller) state) :
    Frame [plan.alias] plan.globals state :=
  entry_frame globals files slots kept

private theorem keep_cell {state next : State} {address : Nat} {cell : Cell}
    (kept : Body.Keeps state.heap.size state next) (found : state.heap[address]? = some cell) :
    next.heap[address]? = some cell :=
  kept.2 _ _ (Array.getElem?_eq_some_iff.mp found).choose found

theorem keeps_frame {aliases globals} {state next : State}
    (frame : Frame aliases globals state) (kept : Body.Keeps state.heap.size state next) :
    Frame aliases globals next := by
  refine ⟨?_, fun binding member => ?_⟩
  · intro first second address atFirst atSecond
    exact frame.1 _ _ _ (kept.1.symm ▸ atFirst) (kept.1.symm ▸ atSecond)
  · obtain ⟨address, value, frozen, owned, found⟩ := frame.2 binding member
    exact ⟨address, value, frozen, kept.1 ▸ owned, keep_cell kept found⟩

private theorem write_other {state : State} {target binding : Binding} {address : Nat}
    (distinct : RootCall.DistinctOwned state) (different : target ≠ binding)
    (owned : state.slots binding = some (.owned address)) (value : Lists.Value) :
    (state.write target value).heap[address]? = state.heap[address]? :=
  RootCall.write_other_cell state target value address (fun hit => different (distinct _ _ _ hit owned))

theorem writes_frame {aliases globals} {state : State} (frame : Frame aliases globals state)
    (target : Binding) (value : Lists.Value) : Frame aliases globals (state.write target value) := by
  have same := write_slots state target value
  refine ⟨?_, fun binding member => ?_⟩
  · intro first second address atFirst atSecond
    exact frame.1 _ _ _ (same ▸ atFirst) (same ▸ atSecond)
  · obtain ⟨address, old, frozen, owned, cell⟩ := frame.2 binding member
    by_cases hit : target = binding
    · subst target
      exact ⟨address, some value, frozen, same.symm ▸ owned, written_cell value owned cell⟩
    · exact ⟨address, old, frozen, same.symm ▸ owned, (write_other frame.1 hit owned value).trans cell⟩

theorem closure_cells_of_contents {first next : State} (kept : KeepsContents first next) :
    KeepsClosureCells first next :=
  by
  refine ⟨fun _ _ _ found => kept _ _ found, ?_⟩
  intro address value flag found
  obtain ⟨frozen, stored⟩ := kept address ⟨.binding value, flag⟩ found
  exact ⟨value, frozen, stored, fun _ => rfl⟩

theorem closure_cells_of_keeps {first next : State} (kept : Body.Keeps first.heap.size first next) :
    KeepsClosureCells first next :=
  closure_cells_of_contents (fun _ cell found => ⟨cell.frozen, keep_cell kept found⟩)

theorem closure_cells_trans {first middle last : State}
    (one : KeepsClosureCells first middle) (two : KeepsClosureCells middle last) :
    KeepsClosureCells first last := by
  refine ⟨?_, ?_⟩
  · intro address closure flag stored
    obtain ⟨middleFlag, found⟩ := one.functions address closure flag stored
    exact two.functions address closure middleFlag found
  · intro address value flag stored
    obtain ⟨middleValue, middleFlag, found, original⟩ := one.bindings address value flag stored
    obtain ⟨finalValue, finalFlag, kept, retained⟩ := two.bindings address middleValue middleFlag found
    refine ⟨finalValue, finalFlag, kept, fun nonempty => ?_⟩
    have same := original nonempty
    exact (retained (same ▸ nonempty)).trans same

theorem write_closure_cells {state : State} {target : Binding} {slot : Nat}
    {frozen : Bool}
    (owned : state.slots target = some (.owned slot))
    (stored : state.heap[slot]? = some ⟨.binding none, frozen⟩) (value : Lists.Value) :
    KeepsClosureCells state (state.write target value) := by
  refine ⟨?_, ?_⟩
  · intro address closure flag found
    have other : state.slots target ≠ some (.owned address) := by
      intro same
      have id : address = slot := by simpa [owned] using same.symm
      subst address
      rw [stored] at found
      cases found
    exact ⟨flag, (RootCall.write_other_cell state target value address other).trans found⟩
  · intro address prior flag found
    by_cases same : address = slot
    · subst address
      have same : prior = none := by
        simp [stored, eq_comm] at found
        exact found.1
      exact ⟨some value, frozen, written_cell value owned stored, fun nonempty => (nonempty same).elim⟩
    · exact ⟨prior, flag, (RootCall.write_other_cell state target value address
        (by simpa [owned, eq_comm] using same)).trans found, fun _ => rfl⟩

theorem write_blank_cells {state : State} {target : Binding} (blank : Blank state target) (value : Lists.Value) :
    KeepsClosureCells state (state.write target value) := by
  obtain ⟨_, _, owned, stored⟩ := blank
  exact write_closure_cells owned stored value

theorem keeps_blank {before after : State} {target : Binding} (blank : Blank before target)
    (kept : Body.Keeps before.heap.size before after) : Blank after target := by
  obtain ⟨address, flag, owned, stored⟩ := blank
  exact ⟨address, flag, kept.1 ▸ owned, keep_cell kept stored⟩

theorem other_blank {state : State} {target writable : Binding}
    (distinct : RootCall.DistinctOwned state) (separate : writable ≠ target)
    (blank : Blank state target) (value : Lists.Value) : Blank (state.write writable value) target := by
  obtain ⟨address, flag, owned, stored⟩ := blank
  exact ⟨address, flag, (write_slots state writable value).symm ▸ owned,
    (write_other distinct separate owned value).trans stored⟩

theorem entered_blank_after_dependency {source : Modules.Source} {caller reached : State}
    (slots : reached.slots = (enter source caller).slots)
    (kept : KeepsContents (enter source caller) reached) {target : Binding}
    (member : target ∈ source.globals.map globalSlot ++ source.fileNames.map fileSlot) :
    Blank reached target := by
  obtain ⟨address, owned, stored⟩ := Entry.entered_blank source caller target member
  obtain ⟨flag, found⟩ := kept _ _ stored
  exact ⟨address, flag, slots ▸ owned, found⟩

theorem keeps_initialized {before after : State} (kept : KeepsClosureCells before after)
    {address : Nat} {value : Lists.Value} {flag : Bool}
    (stored : before.heap[address]? = some ⟨.binding (some value), flag⟩) :
    ∃ frozen, after.heap[address]? = some ⟨.binding (some value), frozen⟩ := by
  obtain ⟨found, frozen, cell, same⟩ := kept.bindings address _ flag stored
  exact ⟨frozen, same (by simp) ▸ cell⟩

private def transport_record {callee : Callable} {defining before after : State} {address : Nat}
    (record : ClosureAt callee.site callee.id defining before address)
    {frozen : Bool}
    (found : after.heap[address]? = some ⟨.function ⟨callee.id, record.captures,
      callee.site.defaultKeys.zip record.defaults⟩, frozen⟩)
    (kept : KeepsClosureCells before after) :
    ClosureAt callee.site callee.id defining after address :=
  { record with
    frozen := frozen
    recorded := found
    live := fun capture member => by
      obtain ⟨value, flag, stored⟩ := record.live capture member
      obtain ⟨next, frozen, cell, _⟩ := kept.bindings capture.address value flag stored
      exact ⟨next, frozen, cell⟩ }

theorem transport_callable {origin program : Program} {state next : State} {callee : Callee} {address : Nat}
    (live : callee.At origin program state address) (kept : KeepsClosureCells state next) :
    callee.At origin program next address := by
  induction live with
  | regular linked record =>
    obtain ⟨_, found⟩ := kept.functions _ _ _ record.recorded
    exact .regular linked (transport_record (callee := _) record found kept)
  | @wrapper _ _ _ declaration id imported _ _ _ _ _ found earlier record captures cell _ ih =>
    obtain ⟨_, stored⟩ := kept.functions _ _ _ record.recorded
    obtain ⟨_, aliasStored⟩ := keeps_initialized kept cell
    exact .wrapper found earlier (transport_record (callee := (Callee.wrapper declaration id imported).layout) record stored kept)
      captures aliasStored ih

theorem keeps_live {aliases : List String} {producer program : Program} {env : Tracked} {state next : State}
    (live : Live aliases producer program env state) (kept : Body.Keeps state.heap.size state next) :
    Live aliases producer program env next := by
  intro name callee tracked
  obtain ⟨slot, address, flag, owned, stored, record⟩ := live name callee tracked
  exact ⟨slot, address, flag, kept.1 ▸ owned, keep_cell kept stored,
    transport_callable record (closure_cells_of_keeps kept)⟩

theorem initial_live {plan : Consumer} {producer program : Program} {state : State} {callee : Callee} {address : Nat}
    (blank : Blank state (fileSlot plan.alias)) (record : callee.At producer program state address) :
    Live [plan.alias] producer program (initial plan.alias callee) (state.write (fileSlot plan.alias) (.function address)) := by
  intro name tracked found
  have hit : name = plan.alias := by
    by_contra different
    simp [initial, track, different] at found
  subst name
  have same : callee = tracked := by simpa [initial, track] using found
  subst tracked
  obtain ⟨slot, frozen, owned, cell⟩ := blank
  refine ⟨slot, address, frozen, ?_, written_cell _ owned cell,
    transport_callable record (write_closure_cells owned cell _)⟩
  simp [readSlot, write_slots, owned]

theorem read_live {aliases : List String} {producer program : Program} {env : Tracked}
    {state : State} {name : String} {callee : Callee}
    (live : Live aliases producer program env state) (tracked : env name = some callee) :
    ∃ address, state.bindingValue (readSlot aliases name) = .ok (.function address) ∧
      callee.At producer program state address := by
  obtain ⟨_, address, _, owned, cell, record⟩ := live name callee tracked
  exact ⟨address, by simp [State.bindingValue, Slot.address, owned, cell], record⟩

theorem write_tracked {aliases : List String} {producer program : Program} {env : Tracked}
    {state : State} {destination : String}
    (blank : Blank state (readSlot aliases destination)) (live : Live aliases producer program env state)
    (value : Lists.Value) (updated : Option Callee)
    (new : ∀ callee, updated = some callee → ∃ address, value = .function address ∧ callee.At producer program state address) :
    Live aliases producer program (track env destination updated) (state.write (readSlot aliases destination) value) := by
  obtain ⟨slot, frozen, owned, cell⟩ := blank
  have slots := write_slots state (readSlot aliases destination) value
  have kept := write_closure_cells owned cell value
  intro name callee found
  by_cases same : name = destination
  · subst name
    obtain ⟨address, equal, record⟩ := new callee (by simpa [track] using found)
    subst value
    exact ⟨slot, address, frozen, slots.symm ▸ owned,
      written_cell _ owned cell, transport_callable record kept⟩
  · obtain ⟨other, address, flag, read, bindingCell, closure⟩ :=
      live name callee (by simpa [track, same] using found)
    obtain ⟨next, stored⟩ := keeps_initialized kept bindingCell
    exact ⟨other, address, next, slots.symm ▸ read, stored, transport_callable closure kept⟩

theorem writes_live {aliases : List String} {producer program : Program} {env : Tracked}
    {state : State} {destination : String}
    (blank : Blank state (globalSlot destination)) (live : Live aliases producer program env state)
    (separate : destination ∉ aliases) (value : Lists.Value) (updated : Option Callee)
    (new : ∀ callee, updated = some callee → ∃ address, value = .function address ∧ callee.At producer program state address) :
    Live aliases producer program (track env destination updated) (state.write (globalSlot destination) value) := by
  have slot : readSlot aliases destination = globalSlot destination := by simp [readSlot, separate]
  exact Eq.mp (congrArg (fun target => Live aliases producer program (track env destination updated) (state.write target value)) slot)
    (write_tracked (slot.symm ▸ blank) live value updated new)

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
