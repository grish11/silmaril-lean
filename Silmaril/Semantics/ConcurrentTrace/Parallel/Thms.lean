module

public import Silmaril.Semantics.ConcurrentTrace.Parallel.Defs
public import Silmaril.Semantics.ConcurrentTrace.Thms
import Silmaril.Proofs.Semantics.ConcurrentTrace.Parallel.Basic

public section

namespace Silmaril.Semantics.ConcurrentTrace

variable {T E : Type*}

/-- An output swap across components leaves both component words unchanged.
An output swap within one component projects to a legal adjacent swap there. -/
theorem shuffle_swap {x y w w' : Word T E} (merge : Brookes.Shuffle x y w)
    (step : AdjacentSwap w w') :
    ∃ x' y', Brookes.Shuffle x' y' w' ∧
      ((x' = x ∧ y' = y) ∨ (AdjacentSwap x x' ∧ y' = y) ∨ (x' = x ∧ AdjacentSwap y y')) :=
  Proofs.Semantics.ConcurrentTrace.Parallel.shuffle_swap merge step

/-- Shuffling saturated word languages produces a saturated word language. -/
theorem shuffleWords_saturated {s t : Set (Word T E)} (hs : Saturated s) (ht : Saturated t) :
    Saturated (shuffleWords s t) :=
  Proofs.Semantics.ConcurrentTrace.Parallel.shuffleWords_saturated hs ht

/-- The output representatives are exactly the shuffles of input representatives. -/
theorem ofTraces_parallel (s t : Set (Trace T E)) :
    ofTraces (parallel s t) = shuffleWords (ofTraces s) (ofTraces t) :=
  Proofs.Semantics.ConcurrentTrace.Parallel.ofTraces_parallel s t

theorem mem_parallel_ofWord {s t : Set (Trace T E)} {w : Word T E} :
    ofWord w ∈ parallel s t ↔ ∃ x y, ofWord x ∈ s ∧ ofWord y ∈ t ∧ Brookes.Shuffle x y w := by
  change w ∈ ofTraces (parallel s t) ↔ _
  rw [ofTraces_parallel]
  exact ⟨fun ⟨x, hx, y, hy, hw⟩ => ⟨x, y, hx, hy, hw⟩, fun ⟨x, y, hx, hy, hw⟩ => ⟨x, hx, y, hy, hw⟩⟩

theorem parallel_assoc (r s t : Set (Trace T E)) :
    parallel (parallel r s) t = parallel r (parallel s t) :=
  Proofs.Semantics.ConcurrentTrace.Parallel.parallel_assoc r s t

theorem parallel_comm (s t : Set (Trace T E)) : parallel s t = parallel t s :=
  Proofs.Semantics.ConcurrentTrace.Parallel.parallel_comm s t

@[simp] theorem parallel_unit_left (s : Set (Trace T E)) : parallel {1} s = s :=
  Proofs.Semantics.ConcurrentTrace.Parallel.parallel_unit_left s

@[simp] theorem parallel_unit_right (s : Set (Trace T E)) : parallel s {1} = s :=
  (parallel_comm _ _).trans (parallel_unit_left s)

theorem parallel_union_left (r s t : Set (Trace T E)) :
    parallel (r ∪ s) t = parallel r t ∪ parallel s t :=
  Proofs.Semantics.ConcurrentTrace.Parallel.parallel_union_left r s t

theorem parallel_union_right (r s t : Set (Trace T E)) :
    parallel r (s ∪ t) = parallel r s ∪ parallel r t := by
  rw [parallel_comm r (s ∪ t), parallel_union_left, parallel_comm s r, parallel_comm t r]

end Silmaril.Semantics.ConcurrentTrace
