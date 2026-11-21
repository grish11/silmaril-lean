module

public import Silmaril.Formats.Bao.Defs

public section

namespace Silmaril.Proofs.Formats.Bao

open Silmaril.Formats.Bao

theorem fold_covered (query : List Interval) (cursor index : Nat)
    (after : cursor ≤ index)
    (before : index < query.foldl (fun next range =>
      if range.start ≤ next then max next range.stop else next) cursor) : Selected query index := by
  induction query generalizing cursor with
  | nil => simp at before; omega
  | cons range tail ih =>
    simp only [List.foldl_cons] at before
    by_cases joins : range.start ≤ cursor
    · rw [ite_eq_left joins] at before
      by_cases inside : index < range.stop
      · exact ⟨range, by simp, by omega, inside⟩
      · obtain ⟨covered, mem, start, stop⟩ := ih (max cursor range.stop) (by omega) before
        exact ⟨covered, List.mem_cons_of_mem _ mem, start, stop⟩
    · rw [ite_eq_right joins] at before
      obtain ⟨covered, mem, start, stop⟩ := ih cursor after before
      exact ⟨covered, List.mem_cons_of_mem _ mem, start, stop⟩

theorem selected_of_data (size group : Nat) (query : List Interval) (span leaf : Span)
    (width index : Nat) (found : Slot.data leaf width ∈ (planAt size group query span).preorder)
    (inside : Contains leaf index) : Selected query index := by
  rw [planAt] at found
  by_cases overlap : overlaps query span = true
  · by_cases small : span.count ≤ 1
    · simp [overlap, small, Plan.preorder] at found
      obtain ⟨rfl, _⟩ := found
      obtain ⟨after, before⟩ := inside
      obtain ⟨range, mem, intersects⟩ := List.any_eq_true.mp overlap
      have ⟨startsBefore, endsAfter⟩ : range.start < leaf.endChunk ∧ leaf.first < range.stop :=
        by simpa using intersects
      simp only [Span.endChunk] at before startsBefore
      exact ⟨range, mem, by omega, by omega⟩
    by_cases grouped : (span.count ≤ group && covers query span) = true
    · simp [overlap, small, grouped, Plan.preorder] at found
      obtain ⟨rfl, _⟩ := found
      have full := (Bool.and_eq_true_iff.mp grouped).2
      simp only [covers, decide_eq_true_eq] at full
      exact fold_covered query leaf.first index inside.1 (Nat.lt_of_lt_of_le inside.2 full)
    · simp [overlap, small, grouped, Plan.preorder] at found
      rcases found with visitedLeft | visitedRight
      · exact selected_of_data size group query span.split.1 leaf width index visitedLeft inside
      · exact selected_of_data size group query span.split.2 leaf width index visitedRight inside
  · simp [Bool.eq_false_iff.mpr overlap, Plan.preorder] at found
termination_by span.count
decreasing_by
  · exact (span.split_decreases (by omega)).2.1
  · exact (span.split_decreases (by omega)).2.2

theorem coverage_at (size group : Nat) (query : List Interval) (span : Span) (index : Nat)
    (inside : Contains span index) (selected : Selected query index) :
    ∃ leaf width, Slot.data leaf width ∈ (planAt size group query span).preorder ∧
      Contains leaf index := by
  obtain ⟨start, stop⟩ := inside
  obtain ⟨range, mem, after, before⟩ := selected
  have overlap : overlaps query span = true := by
    rw [overlaps, List.any_eq_true]
    exact ⟨range, mem, by simp; omega⟩
  rw [planAt]
  by_cases small : span.count ≤ 1
  · exact ⟨span, span.byteSize size, by simp [overlap, small, Plan.preorder], ⟨start, stop⟩⟩
  by_cases grouped : (span.count ≤ group && covers query span) = true
  · exact ⟨span, span.byteSize size, by simp [overlap, small, grouped, Plan.preorder], ⟨start, stop⟩⟩
  have nontrivial : 1 < span.count := by omega
  have decrease := span.split_decreases nontrivial
  have leftEnd : span.split.1.endChunk = span.split.2.first := rfl
  have rightEnd : span.split.2.endChunk = span.endChunk := by
    simp only [Span.split, Span.endChunk] at *
    omega
  by_cases onLeft : index < span.split.2.first
  · obtain ⟨leaf, width, found, contains⟩ := coverage_at size group query span.split.1 index
      ⟨start, leftEnd ▸ onLeft⟩ ⟨range, mem, after, before⟩
    exact ⟨leaf, width, by simp [overlap, small, grouped, Plan.preorder, found], contains⟩
  · have onRight : span.split.2.first ≤ index := by omega
    obtain ⟨leaf, width, found, contains⟩ := coverage_at size group query span.split.2 index
      ⟨onRight, rightEnd ▸ stop⟩ ⟨range, mem, after, before⟩
    exact ⟨leaf, width, by simp [overlap, small, grouped, Plan.preorder, found], contains⟩
termination_by span.count
decreasing_by
  · exact decrease.2.1
  · exact decrease.2.2

theorem pairs_sublist (size group : Nat) (query : List Interval) (span : Span) (postorder : Bool) :
    ((planAt size group query span).pairs postorder).Sublist
      ((planAt size 1 query span).pairs postorder) := by
  rw [planAt.eq_def size group query span, planAt.eq_def size 1 query span]
  by_cases overlap : overlaps query span = true
  · by_cases small : span.count ≤ 1
    · simp [overlap, small]
    have notLeaf : (span.count ≤ 1 && covers query span) = false := by simp [small]
    by_cases grouped : (span.count ≤ group && covers query span) = true
    · simp [overlap, small, grouped, Plan.pairs]
    have left := pairs_sublist size group query span.split.1 postorder
    have right := pairs_sublist size group query span.split.2 postorder
    cases postorder
    · simpa [overlap, small, notLeaf, grouped, Plan.pairs] using
        (left.append right).cons_cons (.pair span)
    · simpa [overlap, small, notLeaf, grouped, Plan.pairs] using
        (left.append right).append (List.Sublist.refl [.pair span])
  · simp [Bool.eq_false_iff.mpr overlap]
termination_by span.count
decreasing_by
  · exact (span.split_decreases (by omega)).2.1
  · exact (span.split_decreases (by omega)).2.2

end Silmaril.Proofs.Formats.Bao
