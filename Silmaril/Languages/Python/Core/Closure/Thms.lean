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
