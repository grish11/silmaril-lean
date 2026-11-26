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

theorem dependency_frame {plan : Consumer} {source : Modules.Source} {caller state : State}
    (globals : source.globals = plan.globals) (files : source.fileNames = [plan.alias])
    (slots : state.slots = (enter source caller).slots) (kept : KeepsContents (enter source caller) state) :
    Frame plan.alias plan.globals state := by
  refine ⟨?_, fun binding marked => ?_⟩
  · intro first second address atFirst atSecond
    exact RootCall.enter_distinct source caller first second address (slots.symm ▸ atFirst) (slots.symm ▸ atSecond)
  · have member : binding ∈ source.globals.map globalSlot ++ source.fileNames.map fileSlot := by
      rw [globals, files]
      simpa [List.mem_append, or_comm] using marked
    obtain ⟨address, owned, blank⟩ := Entry.entered_blank source caller binding member
    obtain ⟨frozen, found⟩ := kept _ _ blank
    exact ⟨address, none, frozen, slots ▸ owned, found⟩

private theorem keep_cell {state next : State} {address : Nat} {cell : Cell}
    (kept : Body.Keeps state.heap.size state next) (found : state.heap[address]? = some cell) :
    next.heap[address]? = some cell :=
  kept.2 _ _ (Array.getElem?_eq_some_iff.mp found).choose found

theorem keeps_frame {importName globals} {state next : State}
    (frame : Frame importName globals state) (kept : Body.Keeps state.heap.size state next) :
    Frame importName globals next := by
  refine ⟨?_, fun binding member => ?_⟩
  · intro first second address atFirst atSecond
    exact frame.1 _ _ _ (kept.1.symm ▸ atFirst) (kept.1.symm ▸ atSecond)
  · obtain ⟨address, value, frozen, owned, found⟩ := frame.2 binding member
    exact ⟨address, value, frozen, kept.1 ▸ owned, keep_cell kept found⟩

theorem keeps_live {importName globals producer program} {env : Tracked importName globals} {state next : State} (live : Live importName producer program env state)
    (kept : Body.Keeps state.heap.size state next) : Live importName producer program env next := by
  intro name callee tracked
  obtain ⟨slot, address, frozen, defining, owned, cell, linked, ⟨closure⟩, inherited⟩ := live name callee tracked
  exact ⟨slot, address, frozen, defining, kept.1 ▸ owned, keep_cell kept cell, linked,
    keep_record (callee := callee.layout) closure kept, kept.1.symm ▸ inherited⟩

private theorem write_other {state : State} {target binding : Binding} {address : Nat}
    (distinct : RootCall.DistinctOwned state) (different : target ≠ binding)
    (owned : state.slots binding = some (.owned address)) (value : Lists.Value) :
    (state.write target value).heap[address]? = state.heap[address]? :=
  RootCall.write_other_cell state target value address (fun hit => different (distinct _ _ _ hit owned))

theorem writes_frame {importName globals} {state : State} (frame : Frame importName globals state)
    (target : Binding) (value : Lists.Value) : Frame importName globals (state.write target value) := by
  have same := write_slots state target value
  refine ⟨?_, fun binding member => ?_⟩
  · intro first second address atFirst atSecond
    exact frame.1 _ _ _ (same ▸ atFirst) (same ▸ atSecond)
  · obtain ⟨address, old, frozen, owned, cell⟩ := frame.2 binding member
    by_cases hit : target = binding
    · subst target
      exact ⟨address, some value, frozen, same.symm ▸ owned, written_cell value owned cell⟩
    · exact ⟨address, old, frozen, same.symm ▸ owned, (write_other frame.1 hit owned value).trans cell⟩

theorem initial_live {plan : Consumer} {producer program : Program} {state defining : State}
    {callee : Callable} {address : Nat} (frame : Frame plan.alias plan.globals state)
    (record : ClosureAt callee.site callee.id defining state address) (linked : callee.Linked producer) :
    Live plan.alias producer program (initial (globals := plan.globals) plan.alias callee) (state.write (fileSlot plan.alias) (.function address)) := by
  intro name tracked found
  have hit : name = plan.alias := by
    by_contra different
    simp [initial, track, different] at found
  subst name
  have same : Callee.regular callee = tracked := by simpa [initial, track] using found
  subst tracked
  obtain ⟨slot, old, frozen, owned, cell⟩ := frame.2 (fileSlot plan.alias) List.mem_cons_self
  refine ⟨slot, address, frozen, defining, ?_, written_cell _ owned cell, linked, write_slot_record record owned cell _, trivial⟩
  simp [readSlot, write_slots, owned]

theorem read_live {importName globals producer program} {env : Tracked importName globals}
    {state : State} {name : String} {callee : Callee importName globals}
    (live : Live importName producer program env state) (tracked : env name = some callee) :
    ∃ address defining, state.bindingValue (readSlot importName name) = .ok (.function address) ∧
      callee.Linked producer program ∧ Nonempty (ClosureAt callee.layout.site callee.layout.id defining state address) ∧
      callee.SharesImport defining.slots state.slots := by
  obtain ⟨_, address, _, defining, owned, cell, linked, record, inherited⟩ := live name callee tracked
  exact ⟨address, defining, by simp [State.bindingValue, Slot.address, owned, cell], linked, record, inherited⟩

theorem writes_live {importName globals producer program} {env : Tracked importName globals} {state : State} {destination : String}
    (frame : Frame importName globals state) (live : Live importName producer program env state) (declared : destination ∈ globals)
    (separate : destination ≠ importName) (value : Lists.Value) (updated : Option (Callee importName globals))
    (new : ∀ callee, updated = some callee → ∃ address defining, value = .function address ∧
      callee.Linked producer program ∧ Nonempty (ClosureAt callee.layout.site callee.layout.id defining state address) ∧
      callee.SharesImport defining.slots state.slots) :
    Live importName producer program (track env destination updated) (state.write (globalSlot destination) value) := by
  obtain ⟨slot, old, frozen, owned, cell⟩ := frame.2 (globalSlot destination)
    (List.mem_cons_of_mem _ (List.mem_map_of_mem declared))
  have slots := write_slots state (globalSlot destination) value
  intro name callee found
  by_cases same : name = destination
  · subst name
    obtain ⟨address, defining, equal, linked, ⟨record⟩, inherited⟩ := new callee (by simpa [track] using found)
    subst value
    exact ⟨slot, address, frozen, defining, by simpa [readSlot, separate, slots] using owned,
      written_cell _ owned cell, linked, write_slot_record (callee := callee.layout) record owned cell _, slots.symm ▸ inherited⟩
  · obtain ⟨other, address, flag, defining, read, bindingCell, linked, ⟨closure⟩, inherited⟩ :=
      live name callee (by simpa [track, same] using found)
    have different : globalSlot destination ≠ readSlot importName name := by
      intro equal
      exact same (by simpa [readSlot, globalSlot, fileSlot, apply_ite] using (congrArg Binding.name equal).symm)
    exact ⟨other, address, flag, defining, slots.symm ▸ read,
      (write_other frame.1 different read value).trans bindingCell, linked, write_slot_record (callee := callee.layout) closure owned cell value, slots.symm ▸ inherited⟩

theorem closure_cells_of_contents {first next : State} (kept : KeepsContents first next) :
    KeepsClosureCells first next :=
  ⟨fun _ _ _ found => kept _ _ found, fun _ value _ found => ⟨value, kept _ _ found⟩⟩

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
    obtain ⟨middleValue, middleFlag, found⟩ := one.bindings address value flag stored
    exact two.bindings address middleValue middleFlag found

theorem write_closure_cells {state : State} {target : Binding} {slot : Nat}
    {old : Option Lists.Value} {frozen : Bool}
    (owned : state.slots target = some (.owned slot))
    (stored : state.heap[slot]? = some ⟨.binding old, frozen⟩) (value : Lists.Value) :
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
      exact ⟨some value, frozen, written_cell value owned stored⟩
    · exact ⟨prior, flag, (RootCall.write_other_cell state target value address
        (by simpa [owned, eq_comm] using same)).trans found⟩

theorem write_global_closure_cells {importName : String} {globals : List String} {state : State}
    (frame : Frame importName globals state) {name : String} (member : name ∈ globals) (value : Lists.Value) :
    KeepsClosureCells state (state.write (globalSlot name) value) := by
  obtain ⟨_, _, _, owned, stored⟩ := frame.2 _ (List.mem_cons_of_mem _ (List.mem_map_of_mem member))
  exact write_closure_cells owned stored value

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
