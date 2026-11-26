module

public import Silmaril.SSA.Isotope.LetIter.Heap.Institution.Trace.Defs
import Silmaril.Proofs.SSA.Isotope.LetIter.Heap.Institution.Trace.Examples

public section

namespace Silmaril.Isotope.LetIter.Heap.TraceExamples

open Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Logic.ITree (TraceReturns)
open Silmaril.Logic.ITree.TraceInstitution (Sat Sentence)

variable {I J : Type}

/-- Reindexing the heap's pointers and the observable events preserves satisfaction. -/
theorem sat_rename (e : I ≃ J) (φ : Sentence.{0,0} (heap I)) :
    Sat (heapModel J) (φ.translate (rename e)) ↔ Sat (heapModel I) φ :=
  Proofs.sat_rename e φ

/-- An allocation reply and the pointer in the next pending read are both renamed. -/
theorem rename_alloc_trace (e : I ≃ J) (i : I) :
    (rename e).trace (.exchange (allocEvent (.inl PUnit.unit)) i (.request (getEvent i)) :
      Trace (Event I) PUnit) =
      .exchange (allocEvent (.inl PUnit.unit)) (e i) (.request (getEvent (e i))) :=
  Proofs.rename_alloc_trace e i

/-- No pending or completed clock operation occurs in a translated heap program. -/
theorem noClock_of_handledTrace {A : Type} (x : (heapClockModel I).State) (t : Tree (Event I) A)
    (p : Trace (heapClock I).toSignature.Event A)
    (h : HandledTrace (heapClockModel I).step x ((heapInclusion I).hom.tree id t) p) : noClock p :=
  Proofs.noClock_of_handledTrace x t p h

/-- The translated allocation sentence accepts only images of heap observations. -/
theorem allocOnce_sat (I : Type) : Sat (heapClockModel I) ((allocOnce I).translate (heapInclusion I)) :=
  Proofs.allocOnce_sat I

/-- A full heap still permits observing the allocation request, but has no
completed allocation exchange or return for this program. -/
theorem alloc_full (s : Store I) (full : ∀ i, s i ≠ none) (p : Trace (Event I) PUnit) :
    HandledTrace (heapModel I).step s (allocOnce I).program p ↔
      p = .prefix ∨ p = .request (allocEvent (.inl PUnit.unit)) :=
  Proofs.alloc_full s full p

/-- The two translated programs can both return unit from the same initial
state after one exchange. Only the allocation observation satisfies `noClock`. -/
theorem same_return_different_history (i : I) :
    ∃ p q : Trace (heapClock I).toSignature.Event PUnit,
      HandledTrace (heapClockModel I).step (emptyStore I, 0)
        ((allocOnce I).translate (heapInclusion I)).program p ∧
      HandledTrace (heapClockModel I).step (emptyStore I, 0)
        (tickOnce.translate (clockInclusion I)).program q ∧
      TraceReturns PUnit.unit 1 p ∧ TraceReturns PUnit.unit 1 q ∧ noClock p ∧ ¬ noClock q :=
  Proofs.same_return_different_history i

end Silmaril.Isotope.LetIter.Heap.TraceExamples
