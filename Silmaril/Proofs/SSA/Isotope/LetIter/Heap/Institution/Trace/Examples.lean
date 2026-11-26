module

public import Silmaril.SSA.Isotope.LetIter.Heap.Institution.Trace.Defs

public section

namespace Silmaril.Isotope.LetIter.Heap.TraceExamples.Proofs

open CategoryTheory Silmaril.Elgot Silmaril.Elgot.ITree
open Silmaril.Logic.ITree (Model TraceReturns)
open Silmaril.Logic.ITree.TraceInstitution (Sat Sentence satisfaction sat_renameState)

variable {I J : Type}

theorem sat_rename (e : I ≃ J) (φ : Sentence.{0,0} (heap I)) :
    Sat (heapModel J) (φ.translate (rename e)) ↔ Sat (heapModel I) φ := by
  have h := congrArg (fun M : Model.{0,0} (heapSignature I) => Sat M φ) (heapModel_reduct e)
  exact (satisfaction (rename e) (heapModel J) φ).trans
    ((Iff.of_eq h).trans (sat_renameState (heapModel I) (storeEquiv e) φ))

theorem rename_alloc_trace (e : I ≃ J) (i : I) :
    (rename e).trace (.exchange (allocEvent (.inl PUnit.unit)) i (.request (getEvent i)) :
      Trace (Event I) PUnit) =
      .exchange (allocEvent (.inl PUnit.unit)) (e i) (.request (getEvent (e i))) :=
  TraceSignature.trace_ofEquiv (S := heap I) (T := heap J) (signatureEquiv e) _

private theorem heapInclusion_noClock {A : Type} (p : Trace (Event I) A) :
    noClock ((heapInclusion I).trace p) := by
  induction p with
  | «prefix» | result | request => trivial
  | exchange _ _ _ ih => exact ih

theorem noClock_of_handledTrace {A : Type} (x : (heapClockModel I).State) (t : Tree (Event I) A)
    (p : Trace (heapClock I).toSignature.Event A)
    (h : HandledTrace (heapClockModel I).step x ((heapInclusion I).hom.tree id t) p) : noClock p := by
  obtain ⟨source, _, rfl⟩ := ((heapInclusion I).handledTrace_image (heapClockModel I).step x t p).mp h
  exact heapInclusion_noClock source

theorem allocOnce_sat (I : Type) : Sat (heapClockModel I) ((allocOnce I).translate (heapInclusion I)) :=
  (satisfaction (heapInclusion I) (heapClockModel I) (allocOnce I)).mpr (fun _ _ _ _ => trivial)

theorem alloc_full (s : Store I) (full : ∀ i, s i ≠ none) (p : Trace (Event I) PUnit) :
    HandledTrace (heapModel I).step s (allocOnce I).program p ↔
      p = .prefix ∨ p = .request (allocEvent (.inl PUnit.unit)) := by
  have hout : out (allocOnce I).program =
      Part.some (.vis (allocEvent (.inl PUnit.unit)) (fun _ => ret PUnit.unit)) := out_vis _ _
  constructor
  · intro h
    cases p with
    | «prefix» => exact Or.inl rfl
    | result a =>
      have eq : out (allocOnce I).program = Part.some (.ret a) := h.1
      rw [hout] at eq
      cases Part.some_injective eq
    | request ev =>
      obtain ⟨k, hk⟩ := h.1
      rw [hout] at hk
      cases Part.some_injective hk
      exact Or.inr rfl
    | exchange ev r tail =>
      obtain ⟨k, hk, _⟩ := h.1
      obtain ⟨y, hy, _⟩ := h.2
      rw [hout] at hk
      cases Part.some_injective hk
      exact (full r hy.1).elim
  · rintro (rfl | rfl)
    · exact ⟨trivial, trivial⟩
    · exact ⟨hasTrace_vis_request _ _, trivial⟩

/-- Both programs can return unit from the same initial store and clock state.
Their finite observations still differ on the no-clock predicate. -/
theorem same_return_different_history (i : I) :
    ∃ p q : Trace (heapClock I).toSignature.Event PUnit,
      HandledTrace (heapClockModel I).step (emptyStore I, 0)
        ((allocOnce I).translate (heapInclusion I)).program p ∧
      HandledTrace (heapClockModel I).step (emptyStore I, 0)
        (tickOnce.translate (clockInclusion I)).program q ∧
      TraceReturns PUnit.unit 1 p ∧ TraceReturns PUnit.unit 1 q ∧ noClock p ∧ ¬ noClock q := by
  let v : Value I := .inl PUnit.unit
  let p : Trace (Event I) PUnit := .exchange (allocEvent v) i (.result PUnit.unit)
  let q : Trace Clock PUnit := .exchange Clock.tick true (.result PUnit.unit)
  have hp : HandledTrace ((heapInclusion I).hom.restrict (heapClockModel I).step) (emptyStore I, 0)
      (allocOnce I).program p := by
    refine ⟨⟨_, out_vis _ _, out_ret _⟩, (write (emptyStore I) i (some v), 0), ?_, trivial⟩
    exact ⟨i, rfl, ⟨rfl, rfl⟩, rfl⟩
  have hq : HandledTrace ((clockInclusion I).hom.restrict (heapClockModel I).step) (emptyStore I, 0)
      tickOnce.program q := by
    exact ⟨⟨_, out_vis _ _, out_ret _⟩, (emptyStore I, 1), ⟨true, rfl, ⟨rfl, rfl⟩, rfl⟩, trivial⟩
  refine ⟨(heapInclusion I).trace p, (clockInclusion I).trace q, ?_, ?_, rfl, rfl,
    heapInclusion_noClock p, id⟩
  · exact ((heapInclusion I).handledTrace_image _ _ _ _).mpr ⟨p, hp, rfl⟩
  · exact ((clockInclusion I).handledTrace_image _ _ _ _).mpr ⟨q, hq, rfl⟩

end Silmaril.Isotope.LetIter.Heap.TraceExamples.Proofs
