module

public import Silmaril.Languages.Python.Core.Closure.Defs
import Silmaril.Proofs.Languages.Python.Core.Closure.Environment

public section

namespace Silmaril.Languages.Python.Core.Closure

theorem Heap.lookup_reserve_old (heap : Heap) (count : Nat) (identity : CellId)
    (live : identity.address < heap.next) :
    (heap.reserve count).lookup identity = heap.lookup identity :=
  Proofs.Languages.Python.Core.Closure.lookup_reserve_old heap count identity live

theorem Heap.lookup_reserve_new (heap : Heap) (count : Nat) (identity : CellId)
    (lower : heap.next ≤ identity.address) (upper : identity.address < heap.next + count) :
    (heap.reserve count).lookup identity = some none :=
  Proofs.Languages.Python.Core.Closure.lookup_reserve_new heap count identity lower upper

theorem Heap.allocate_write (heap : Heap) (value : Value) :
    (heap.reserve 1).write (heap.allocate value).1 value = some (heap.allocate value).2 := by
  simp [Heap.allocate, Heap.write, Heap.reserve]
  rfl

theorem Heap.lookup_allocate_old (heap : Heap) (value : Value) (identity : CellId)
    (live : identity.address < heap.next) :
    (heap.allocate value).2.lookup identity = heap.lookup identity := by
  simp [Heap.allocate, Heap.lookup, Heap.reserve, live, Nat.ne_of_lt live,
    Nat.lt_trans live (Nat.lt_succ_self heap.next)]

theorem Heap.lookup_allocate_new (heap : Heap) (value : Value) :
    (heap.allocate value).2.lookup (heap.allocate value).1 = some (some value) := by
  simp [Heap.allocate, Heap.lookup, Heap.reserve]

theorem Heap.allocate_frontier (heap : Heap) (value : Value) :
    (heap.allocate value).1.address = heap.next ∧ (heap.allocate value).2.next = heap.next + 1 :=
  ⟨rfl, rfl⟩

theorem Heap.allocate_distinct (heap : Heap) (first second : Value) :
    ((heap.allocate first).2.allocate second).1 ≠ (heap.allocate first).1 := by
  simp [Heap.allocate, Heap.reserve]

theorem Heap.materializeFreshTuple_empty (heap : Heap) :
    heap.materializeFreshTuple [] = (.tuple [], heap) := rfl

theorem Heap.materializeFreshTuple_nonempty (heap : Heap) (head : Core.Module.TupleDispatch.Element)
    (tail : List Core.Module.TupleDispatch.Element) :
    heap.materializeFreshTuple (head :: tail) =
      (.tupleObject ⟨some heap.next, head :: tail⟩, (heap.allocate (.tuple (head :: tail))).2) := rfl

theorem Heap.materializeFreshTuple_distinct (heap : Heap) (first second : Core.Module.TupleDispatch.Element)
    (restFirst restSecond : List Core.Module.TupleDispatch.Element) :
    let (object, reached) := heap.materializeFreshTuple (first :: restFirst)
    object ≠ (reached.materializeFreshTuple (second :: restSecond)).1 := by
  simp [Heap.materializeFreshTuple, Heap.allocate, Heap.reserve]

theorem Heap.moduleTuple_empty (heap : Heap) (items : List GlobalTupleItem) :
    heap.materializeModuleTuple items [] = (.tuple [], heap) ∧
      (Value.tuple []).tupleObject? = some ⟨none, []⟩ := ⟨rfl, rfl⟩

theorem Heap.moduleTuple_closed (heap : Heap) (items : List GlobalTupleItem)
    (values : List Core.Module.TupleDispatch.Element) (closed : items.any GlobalTupleItem.isRead = false) :
    heap.materializeModuleTuple items values = (.tuple values, heap) := by
  cases values <;> simp [Heap.materializeModuleTuple, closed]

theorem Heap.moduleTuple_closedOrigin (heap : Heap) (items : List GlobalTupleItem)
    (head : Core.Module.TupleDispatch.Element) (tail : List Core.Module.TupleDispatch.Element) (closed : items.any GlobalTupleItem.isRead = false) :
    heap.materializeModuleTuple items (head :: tail) true =
      (.tupleObject (heap.saveTupleOrigin head tail).1, (heap.saveTupleOrigin head tail).2) := by
  simp [Heap.materializeModuleTuple, closed]

theorem Heap.moduleTuple_fresh (heap : Heap) (items : List GlobalTupleItem)
    (head : Core.Module.TupleDispatch.Element) (tail : List Core.Module.TupleDispatch.Element)
    (reads : items.any GlobalTupleItem.isRead = true) :
    heap.materializeModuleTuple items (head :: tail) =
      (.tupleObject ⟨some heap.next, head :: tail⟩, (heap.allocate (.tuple (head :: tail))).2) := by
  simp [Heap.materializeModuleTuple, Heap.materializeFreshTuple, reads, Heap.allocate]

theorem Heap.write_spec {heap updated : Heap} {identity : CellId} {value : Value}
    (write : heap.write identity value = some updated) :
    updated.next = heap.next ∧ updated.lookup identity = some (some value) ∧
      ∀ other, other ≠ identity → updated.lookup other = heap.lookup other :=
  Proofs.Languages.Python.Core.Closure.heap_write_spec write

theorem Frame.fresh_owned_unbound (heap : Heap) {layout : Layout}
    (captures : Fin layout.captures → CellId) (index : Fin layout.owned) :
    let (updated, frame) := Frame.fresh heap captures
    updated.lookup (frame.owned index) = some none :=
  Proofs.Languages.Python.Core.Closure.fresh_owned_unbound heap captures index

theorem Frame.fresh_owned_injective (heap : Heap) {layout : Layout}
    (captures : Fin layout.captures → CellId) :
    Function.Injective (Frame.fresh heap captures).2.owned :=
  Proofs.Languages.Python.Core.Closure.fresh_owned_injective heap captures

theorem Frame.fresh_capture (heap : Heap) {layout : Layout} (captures : Fin layout.captures → CellId)
    (index : Fin layout.captures) : (Frame.fresh heap captures).2.captures index = captures index :=
  rfl

theorem Frame.capture_at {layout : Layout} (frame : Frame layout) (code : CodeRef)
    (select : Fin code.layout.captures → CaptureSlot layout) (index : Fin code.layout.captures) :
    (frame.closure code select).captures[index] = frame.captureCell (select index) :=
  Proofs.Languages.Python.Core.Closure.capture_at frame code select index

theorem Function.ofCaptureList_order (code : CodeRef) (captures : List CellId)
    (size : captures.length = code.layout.captures) :
    (Function.ofCaptureList code captures size).captures.toList = captures := by
  simp [Function.ofCaptureList, Vector.toList]

theorem Frame.writeCell_spec {layout : Layout} {frame updatedFrame : Frame layout}
    {heap updatedHeap : Heap} {identity : CellId} {value : Value}
    (write : frame.writeCell heap identity value = .ok (updatedHeap, updatedFrame)) :
    updatedFrame = frame ∧ heap.write identity value = some updatedHeap :=
  Proofs.Languages.Python.Core.Closure.writeCell_spec write

theorem Frame.read_capture_after_owned_write {layout : Layout} {frame updatedFrame : Frame layout}
    {heap updatedHeap : Heap} {owned : Fin layout.owned} {capture : Fin layout.captures} {value : Value}
    (aliases : frame.owned owned = frame.captures capture)
    (write : frame.write heap (.owned owned) value = .ok (updatedHeap, updatedFrame)) :
    updatedFrame = frame ∧ updatedFrame.read updatedHeap (.capture capture) = .ok value :=
  Proofs.Languages.Python.Core.Closure.read_capture_after_owned_write aliases write

end Silmaril.Languages.Python.Core.Closure
