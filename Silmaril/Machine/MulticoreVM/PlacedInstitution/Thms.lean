module

public import Silmaril.Machine.MulticoreVM.Institution.Placed.Thms

/-! # Quotient behavior of the placed VM

`placedToNamed ≫ namedToConcurrent` observes the thread swap class of a placed
word. Its direct image agrees with taking the two images in sequence.
Applied to `ofPlaced`, each class has a successful finite run as a witness.
Instruction refinement gives inclusion in the abstract concurrent model.
-/

public section

namespace Silmaril.Machine.MulticoreVM.Institution

open CategoryTheory
open Silmaril.Semantics.ConcurrentTrace (ofWord)

universe u

variable {A : Sig.{u}} {Core Thread Choice : Type u}

/-- Applying both observation maps at once gives the same behavior as taking
first the named image and then the quotient image. -/
theorem placed_concurrent_image (M : Model A.PlacedWord) :
    ((placedToNamed ≫ namedToConcurrent).app A) '' M =
      (namedToConcurrent.app A) '' ((placedToNamed.app A) '' M) :=
  (Set.image_image (namedToConcurrent.app A) (placedToNamed.app A) M).symm

variable [DecidableEq A.CoreId]

/-- A projected physical trace is admitted exactly when a successful finite
placed schedule emits a word in that thread trace class. -/
theorem mem_placed_concurrent_iff
    (instruction : Placed.Instruction A.CoreId A.ThreadId Core Thread Choice A.Event)
    (initial : Placed.Config A.CoreId A.ThreadId Core Thread) (trace : A.ConcurrentTrace) :
    trace ∈ ((placedToNamed ≫ namedToConcurrent).app A) '' ofPlaced (A := A) instruction initial ↔
      ∃ schedule word final, Placed.Scheduled instruction schedule initial word final ∧
        ofWord (Placed.threadWord word) = trace := by
  constructor
  · exact fun ⟨word, ⟨schedule, final, run⟩, eq⟩ => ⟨schedule, word, final, run, eq⟩
  · exact fun ⟨schedule, word, final, run, eq⟩ => ⟨word, ⟨schedule, final, run⟩, eq⟩

/-- Under instruction refinement every projected placed trace is admitted by
the abstract VM from the initial thread store. -/
theorem placed_concurrent_subset
    {instruction : Placed.Instruction A.CoreId A.ThreadId Core Thread Choice A.Event}
    {step : Transition (A.ThreadId → Option Thread) A.ThreadId Choice A.Event}
    (refines : instruction.Refines step) (initial : Placed.Config A.CoreId A.ThreadId Core Thread) :
    ((placedToNamed ≫ namedToConcurrent).app A) '' ofPlaced (A := A) instruction initial ⊆
      concurrentModel (A := A) step initial.threads := by
  rw [placed_concurrent_image]
  calc
    _ ⊆ (namedToConcurrent.app A) '' namedModel (A := A) step initial.threads :=
      Set.image_mono (placed_named_subset refines initial)
    _ = _ := image_ofVM (namedToConcurrent.app A) id step initial.threads

end Silmaril.Machine.MulticoreVM.Institution
