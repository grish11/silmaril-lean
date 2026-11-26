module

import Silmaril.Semantics.ConcurrentTrace.Ideals.Thms
import Mathlib.Order.FixedPoints
import Mathlib.Data.Set.Countable

namespace Silmaril.Proofs.Semantics.ConcurrentTrace.Ideals.Regression

open Silmaril.Semantics.ConcurrentTrace Silmaril.Semantics.ConcurrentTrace.Ideals

/-- The fully commuting two-letter alphabet, represented by the two multiplicities. -/
private def letters : WordMap Bool (Nat × Nat) where
  toFun w := (w.count false, w.count true)
  preservesPrefix := by
    intro w v h
    obtain ⟨tail, rfl⟩ := List.prefix_iff_exists_append_eq.mp h
    exact ⟨by simp [List.count_append], by simp [List.count_append]⟩

private def left : Nat → Bool
  | 0 => false
  | _ + 1 => true

private def right : Nat → Bool
  | 0 => true
  | 1 => false
  | _ + 2 => true

/-- One front swap changes the first representative cut. The two infinite sequences
still have the same ideal because their cuts agree in the quotient from length two on. -/
example :
    Trace.ofSequence letters (.infinite left : PartialSequence Bool Unit) =
      Trace.ofSequence letters (.infinite right) ∧
    letters ((.infinite left : PartialSequence Bool Unit).cut 1) ≠
      letters ((.infinite right : PartialSequence Bool Unit).cut 1) := by
  constructor
  · apply Trace.observe_injective
    refine Prod.ext (prefixIdeal_eq_of_cofinal_eq letters _ _ ?_) rfl
    intro n
    refine ⟨n + 2, by omega, ?_⟩
    simp [PartialSequence.cut, List.ofFn_succ, left, right, letters, Nat.add_comm,
      Nat.add_left_comm]
  · decide

/-- One visible unit event precedes the selected whole trace. -/
private def emit : PartialSequence Unit Unit → PartialSequence Unit Unit
  | .pending w => .pending (() :: w)
  | .done w r => .done (() :: w) r
  | .infinite f => .infinite (fun | 0 => () | n + 1 => f n)

private def wholeStep : Set (PartialSequence Unit Unit) →o Set (PartialSequence Unit Unit) :=
  ⟨Set.image emit, fun _ _ h => Set.image_mono h⟩

private def forever : PartialSequence Unit Unit := .infinite (fun _ => ())

/-- Whole-trace may semantics with the empty set as bottom picks no trace for the loop,
even though the endlessly emitting trace alone also solves its unfolding equation. -/
example : wholeStep.lfp = ∅ ∧ wholeStep {forever} = {forever} := by
  refine ⟨le_antisymm (OrderHom.lfp_le wholeStep ?_) bot_le, ?_⟩
  · change emit '' (∅ : Set (PartialSequence Unit Unit)) ⊆ ∅
    rw [Set.image_empty]
  · have he : emit forever = forever := by
      unfold emit forever
      congr
    change emit '' {forever} = {forever}
    rw [Set.image_singleton, he]

/-- The same loop observed by lengths of finite prefixes always supplies the empty
prefix, and each unfolding adds one event to the available prefix observations. -/
private def prefixStep : Set Nat →o Set Nat where
  toFun p := {0} ∪ Nat.succ '' p
  monotone' := fun _ _ h => Set.union_subset_union_right _ (Set.image_mono h)

example : prefixStep.lfp = Set.univ := by
  apply Set.eq_univ_of_forall
  intro n
  induction n with
  | zero =>
    rw [← OrderHom.map_lfp prefixStep]
    exact Or.inl rfl
  | succ n ih =>
    rw [← OrderHom.map_lfp prefixStep]
    exact Or.inr ⟨n, ih, rfl⟩

/-- The ideal of all finite subsets of an uncountable alphabet cannot be observed
along any one sequence. Each cut contributes only a finite set. -/
example {A : Type*} [DecidableEq A] [Uncountable A] (q : WordMap A (Finset A))
    (s : PartialSequence A Unit) : prefixIdeal q s ≠ (⊤ : Order.Ideal (Finset A)) := by
  intro h
  have covers : ⋃ n, (q (s.cut n) : Set A) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro a
    have mem : {a} ∈ prefixIdeal q s := by rw [h]; trivial
    obtain ⟨n, hn⟩ := (mem_prefixIdeal q s {a}).1 mem
    exact Set.mem_iUnion.2 ⟨n, hn (Finset.mem_singleton_self a)⟩
  have countable := Set.countable_iUnion (fun n => (q (s.cut n)).finite_toSet.countable)
  exact Set.not_countable_univ (covers ▸ countable)

end Silmaril.Proofs.Semantics.ConcurrentTrace.Ideals.Regression
