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

theorem keeps_live {importName program env} {state next : State} (live : Live importName program env state)
    (kept : Body.Keeps state.heap.size state next) : Live importName program env next := by
  intro name callee tracked
  obtain ⟨slot, address, frozen, defining, owned, cell, linked, ⟨closure⟩⟩ := live name callee tracked
  exact ⟨slot, address, frozen, defining, kept.1 ▸ owned, keep_cell kept cell, linked,
    keep_record (callee := callee) closure kept⟩

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

theorem initial_live {plan : Consumer} {program : Program} {state defining : State}
    {callee : Callable} {address : Nat} (frame : Frame plan.alias plan.globals state)
    (record : ClosureAt callee.site callee.id defining state address) (linked : callee.Linked program) :
    Live plan.alias program (initial plan.alias callee) (state.write (fileSlot plan.alias) (.function address)) := by
  intro name tracked found
  have hit : name = plan.alias := by
    by_contra different
    simp [initial, update, different] at found
  subst name
  have same : callee = tracked := by simpa [initial, update] using found
  subst tracked
  obtain ⟨slot, old, frozen, owned, cell⟩ := frame.2 (fileSlot plan.alias) List.mem_cons_self
  refine ⟨slot, address, frozen, defining, ?_, written_cell _ owned cell, linked, write_slot_record record owned cell _⟩
  simp [readSlot, write_slots, owned]

theorem read_live {importName program env} {state : State} {name : String} {callee : Callable}
    (live : Live importName program env state) (tracked : env name = some callee) :
    ∃ address defining, state.bindingValue (readSlot importName name) = .ok (.function address) ∧
      callee.Linked program ∧ Nonempty (ClosureAt callee.site callee.id defining state address) := by
  obtain ⟨_, address, _, defining, owned, cell, linked, record⟩ := live name callee tracked
  exact ⟨address, defining, by simp [State.bindingValue, Slot.address, owned, cell], linked, record⟩

theorem writes_live {importName globals program env} {state : State} {destination : String}
    (frame : Frame importName globals state) (live : Live importName program env state) (declared : destination ∈ globals)
    (separate : destination ≠ importName) (value : Lists.Value) (updated : Option Callable)
    (new : ∀ callee, updated = some callee → ∃ address defining, value = .function address ∧
      callee.Linked program ∧ Nonempty (ClosureAt callee.site callee.id defining state address)) :
    Live importName program (update env destination updated) (state.write (globalSlot destination) value) := by
  obtain ⟨slot, old, frozen, owned, cell⟩ := frame.2 (globalSlot destination)
    (List.mem_cons_of_mem _ (List.mem_map_of_mem declared))
  have slots := write_slots state (globalSlot destination) value
  intro name callee found
  by_cases same : name = destination
  · subst name
    obtain ⟨address, defining, equal, linked, ⟨record⟩⟩ := new callee (by simpa [update] using found)
    subst value
    exact ⟨slot, address, frozen, defining, by simpa [readSlot, separate, slots] using owned,
      written_cell _ owned cell, linked, write_slot_record record owned cell _⟩
  · obtain ⟨other, address, flag, defining, read, bindingCell, linked, ⟨closure⟩⟩ :=
      live name callee (by simpa [update, same] using found)
    have different : globalSlot destination ≠ readSlot importName name := by
      intro equal
      exact same (by simpa [readSlot, globalSlot, fileSlot, apply_ite] using (congrArg Binding.name equal).symm)
    exact ⟨other, address, flag, defining, slots.symm ▸ read,
      (write_other frame.1 different read value).trans bindingCell, linked, write_slot_record closure owned cell value⟩

end Silmaril.Proofs.Languages.Starlark.Modules.Resolve.Capture.Trace.Published.Imports
