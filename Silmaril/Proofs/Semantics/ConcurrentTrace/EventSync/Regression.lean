module

import Silmaril.Semantics.ConcurrentTrace.EventSync.Thms

namespace Silmaril.Proofs.Semantics.ConcurrentTrace.EventSync.Regression

open Silmaril.Semantics.ConcurrentTrace
open Silmaril.Semantics.ConcurrentTrace.EventSync

private def event : Letter Bool Unit := .event false ()
private def syncLetter : Letter Bool Unit := .sync [true, true]

/-- An event can cross a sync that omits its thread, even when the sync repeats
a participant. The observation still retains the result and final used names. -/
example :
    includeFinite (ofWord [event, syncLetter]) (some (false, ({false, true} : Set Bool))) =
      includeFinite (ofWord [syncLetter, event]) (some (false, ({false, true} : Set Bool))) := by
  have independent : event.Independent syncLetter := .eventSync (by simp)
  rw [ofWord_cons, ofWord_cons, ofWord_cons, ofWord_cons, ofWord_nil, mul_one, mul_one]
  rw [swap independent]

/-- Repeating a concrete event indefinitely cannot have a principal finite-prefix ideal. -/
example (t : Trace Bool Unit) :
    Ideals.prefixIdeal wordMap (.infinite (fun _ => event) : PartialSequence _ Unit) ≠
      Order.Ideal.principal t :=
  Ideals.prefixIdeal_infinite_ne_principal wordMap lengthOrder length_ofWord _ t

private def emit (thread : Bool) : ThreadTrace.Alloc Bool (FreeMonoid (Letter Bool Unit)) Unit :=
  fun _ used => WriterT.mk (pure (((), used), FreeMonoid.of (Letter.event thread ())))

/-- The continuation emits on the fresh thread and keeps the extended used set,
including after its output is quotiented. -/
example :
    (((), insert true ({false} : Set Bool)), singleton (Letter.event true ())) ∈
      (ThreadTrace.Alloc.mapOutput quotientOutput (ThreadTrace.fresh >>= emit)).run false {false} := by
  rw [ThreadTrace.Alloc.mem_mapOutput]
  refine ⟨FreeMonoid.of (.event true ()), ?_, rfl⟩
  rw [ThreadTrace.Alloc.mem_bind]
  refine ⟨true, insert true {false}, 1, FreeMonoid.of (.event true ()), ?_, rfl, one_mul _⟩
  rw [ThreadTrace.mem_fresh]
  simp

end Silmaril.Proofs.Semantics.ConcurrentTrace.EventSync.Regression
