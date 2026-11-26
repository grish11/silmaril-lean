module

public import Silmaril.Languages.Python.Core.Module.TupleDispatch.Defs

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
  simp [construct, prepared]

theorem construct_argument_failure (heap reached : Heap) (binding : TypeBinding) (error : Failure)
    (argument : Heap → Except Failure Object × Heap)
    (failed : argument heap = (.error error, reached)) :
    construct heap (some binding) (some argument) = (.error error, reached) := by
  simp [construct, failed]

theorem construct_nonCallable (heap reached : Heap) (object : Object)
    (argument : Heap → Except Failure Object × Heap)
    (prepared : argument heap = (.ok object, reached)) :
    construct heap (some .nonCallable) (some argument) = (.error .notCallable, reached) := by
  simp [construct, prepared]

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

end Silmaril.Languages.Python.Core.Module.TupleDispatch
