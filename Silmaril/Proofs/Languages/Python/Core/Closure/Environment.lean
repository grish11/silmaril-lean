module

public import Silmaril.Languages.Python.Core.Closure.Defs
import Init.Data.Vector.OfFn

public section

namespace Silmaril.Proofs.Languages.Python.Core.Closure

open Silmaril.Languages.Python.Core.Closure

theorem lookup_reserve_old (heap : Heap) (count : Nat) (identity : CellId)
    (live : identity.address < heap.next) :
    (heap.reserve count).lookup identity = heap.lookup identity := by
  have stillLive : identity.address < heap.next + count := by omega
  simp [Heap.lookup, Heap.reserve, live, stillLive]

theorem lookup_reserve_new (heap : Heap) (count : Nat) (identity : CellId)
    (lower : heap.next ≤ identity.address) (upper : identity.address < heap.next + count) :
    (heap.reserve count).lookup identity = some none := by
  have fresh : ¬ identity.address < heap.next := by omega
  simp [Heap.lookup, Heap.reserve, fresh, upper]

theorem heap_write_spec {heap updated : Heap} {identity : CellId} {value : Value}
    (write : heap.write identity value = some updated) :
    updated.next = heap.next ∧ updated.lookup identity = some (some value) ∧
      ∀ other, other ≠ identity → updated.lookup other = heap.lookup other := by
  by_cases live : identity.address < heap.next
  · simp only [Heap.write, live, ite_true, Option.some.injEq] at write
    subst updated
    refine ⟨rfl, by simp [Heap.lookup, live], fun other different => ?_⟩
    have differentAddress : other.address ≠ identity.address := by
      intro address
      apply different
      cases other
      cases identity
      cases address
      rfl
    simp [Heap.lookup, differentAddress]
  · simp [Heap.write, live] at write

theorem fresh_owned_unbound (heap : Heap) {layout : Layout}
    (captures : Fin layout.captures → CellId) (index : Fin layout.owned) :
    let (updated, frame) := Frame.fresh heap captures
    updated.lookup (frame.owned index) = some none := by
  change (heap.reserve layout.owned).lookup ⟨heap.next + index.val⟩ = some none
  refine lookup_reserve_new _ _ _ ?_ ?_
  · change heap.next ≤ heap.next + index.val
    omega
  · change heap.next + index.val < heap.next + layout.owned
    exact Nat.add_lt_add_left index.isLt _

theorem fresh_owned_injective (heap : Heap) {layout : Layout}
    (captures : Fin layout.captures → CellId) :
    Function.Injective (Frame.fresh heap captures).2.owned := by
  intro first second eq
  have address := congrArg CellId.address eq
  change heap.next + first.val = heap.next + second.val at address
  exact Fin.ext (by omega)

theorem capture_at {layout : Layout} (frame : Frame layout) (code : CodeRef)
    (select : Fin code.layout.captures → CaptureSlot layout) (index : Fin code.layout.captures) :
    (frame.closure code select).captures[index] = frame.captureCell (select index) := by
  change (Vector.ofFn (frame.captureCell ∘ select))[index.val]'index.isLt = frame.captureCell (select index)
  exact Vector.getElem_ofFn index.isLt

theorem writeCell_spec {layout : Layout} {frame updatedFrame : Frame layout}
    {heap updatedHeap : Heap} {identity : CellId} {value : Value}
    (write : frame.writeCell heap identity value = .ok (updatedHeap, updatedFrame)) :
    updatedFrame = frame ∧ heap.write identity value = some updatedHeap := by
  cases update : heap.write identity value with
  | none => simp [Frame.writeCell, update] at write
  | some next =>
    simp only [Frame.writeCell, update, Except.ok.injEq, Prod.mk.injEq] at write
    obtain ⟨rfl, rfl⟩ := write
    exact ⟨rfl, rfl⟩

theorem read_capture_after_owned_write {layout : Layout} {frame updatedFrame : Frame layout}
    {heap updatedHeap : Heap} {owned : Fin layout.owned} {capture : Fin layout.captures} {value : Value}
    (aliases : frame.owned owned = frame.captures capture)
    (write : frame.write heap (.owned owned) value = .ok (updatedHeap, updatedFrame)) :
    updatedFrame = frame ∧ updatedFrame.read updatedHeap (.capture capture) = .ok value := by
  have ⟨frameSame, cellWrite⟩ := writeCell_spec
    (show frame.writeCell heap (frame.owned owned) value = .ok (updatedHeap, updatedFrame) from write)
  subst updatedFrame
  have lookup := (heap_write_spec cellWrite).2.1
  exact ⟨rfl, by simp [Frame.read, Heap.read, ← aliases, lookup]⟩

end Silmaril.Proofs.Languages.Python.Core.Closure
