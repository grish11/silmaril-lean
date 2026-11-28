module

public import Silmaril.Languages.Python.Core.Module.TupleDispatch.Defs
public import Silmaril.Languages.Python.Core.Module.ListObject.Thms

public section

namespace Silmaril.Languages.Python.Core.Module.TupleDispatch

theorem materialize_empty (heap : Heap) : heap.materialize [] = (⟨none, []⟩, heap) := rfl

theorem construct_missing (heap : Heap) (argument : Option (Heap → Except Failure Object × Heap)) :
    construct heap none argument = (.error .missingType, heap) := rfl

theorem construct_empty (heap : Heap) :
    construct heap (some .stockTuple) none = (.ok ⟨none, []⟩, heap) := rfl

theorem construct_exact (heap reached : Heap) (object : Object)
    (argument : Heap → Except Failure Object × Heap)
    (prepared : argument heap = (.ok object, reached)) :
    construct heap (some .stockTuple) (some argument) = (.ok object, reached) := by
  simp [construct, constructWith, prepared, Except.bind]

theorem construct_argument_failure (heap reached : Heap) (binding : TypeBinding) (error : Failure)
    (argument : Heap → Except Failure Object × Heap)
    (failed : argument heap = (.error error, reached)) :
    construct heap (some binding) (some argument) = (.error error, reached) := by
  simp [construct, constructWith, failed, Except.bind]

theorem construct_nonCallable (heap reached : Heap) (object : Object)
    (argument : Heap → Except Failure Object × Heap)
    (prepared : argument heap = (.ok object, reached)) :
    construct heap (some .nonCallable) (some argument) = (.error .notCallable, reached) := by
  simp [construct, constructWith, prepared, Except.bind]

theorem concat_empty_left (heap : Heap) (left right : Object) (empty : left.contents = []) :
    concat heap left right = (right, heap) := by simp [concat, empty]

theorem concat_empty_right (heap : Heap) (left right : Object) (nonempty : left.contents ≠ [])
    (empty : right.contents = []) : concat heap left right = (left, heap) := by
  simp [concat, nonempty, empty]

theorem concat_nonempty (heap : Heap) (left right : Object)
    (leftPresent : left.contents ≠ []) (rightPresent : right.contents ≠ []) :
    concat heap left right =
      (⟨some heap.objects.size, left.contents ++ right.contents⟩,
        ⟨heap.objects.push (left.contents ++ right.contents)⟩) := by
  cases left with | mk address contents => cases contents <;> simp_all [concat, Heap.materialize]

theorem callUnbound_lookup_failure (heap : Heap) (binding : Option TypeBinding) (method : Method)
    (receiver argument : Literal) (error : Failure) (failed : lookupUnbound binding method = .error error) :
    callUnbound heap binding method receiver argument = (.error error, heap) := by simp [callUnbound, failed]

/-- Descriptor checking happens after the second argument has been prepared. -/
theorem callUnbound_list_receiver (heap : Heap) (method : Method)
    (receiver : List Core.Module.Value) (argument : Literal) :
    callUnbound heap (some .stockTuple) method (.list receiver) argument =
      (.error (.wrongReceiver method), (argument.prepare heap).2) := rfl

theorem direct_eq_list (heap : Heap) (receiver : Object) (argument : List Core.Module.Value) :
    (BoundMethod.mk .eq receiver).invoke heap (.list argument) = (.ok .notImplemented, heap) ∧
      equal receiver (.list argument) = false := ⟨rfl, rfl⟩

theorem equalContents_text_cons (left right : Core.Text) (leftRest rightRest : List Element) :
    equalContents (.text left :: leftRest) (.text right :: rightRest) =
      (decide (left.points = right.points) && equalContents leftRest rightRest) := rfl

theorem constructFromListDisplay_missing (heap : ListHeap) (contents : List Value) :
    constructFromListDisplay heap none contents = (.error .missingType, heap) := rfl

theorem constructFromListDisplay_stock (heap : ListHeap) (contents : List Value) :
    constructFromListDisplay heap (some .stockTuple) contents = (.ok contents, (heap.allocate contents).2) := by
  have read : (heap.allocate contents).2.lookup (heap.allocate contents).1.address = some contents :=
    (ListHeap.allocate_lookup_new heap contents).2
  simp [constructFromListDisplay, constructWith, Except.bind, read]

theorem constructFromListDisplay_stock_lookup (heap : ListHeap) (contents : List Value) :
    (constructFromListDisplay heap (some .stockTuple) contents).2.lookup (heap.allocate contents).1.address =
      some contents := by
  rw [constructFromListDisplay_stock]
  exact (ListHeap.allocate_lookup_new heap contents).2

theorem constructFromListDisplay_mask (heap : ListHeap) (contents : List Value) :
    constructFromListDisplay heap (some .noneValue) contents = (.error .notCallable, (heap.allocate contents).2) ∧
      constructFromListDisplay heap (some .nonCallable) contents =
        (.error .notCallable, (heap.allocate contents).2) :=
  ⟨rfl, rfl⟩

end Silmaril.Languages.Python.Core.Module.TupleDispatch
