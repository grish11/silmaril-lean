module

public import Silmaril.Formats.Dasl.SparseRangeSet.Defs

public section

namespace Silmaril.Proofs.Formats.Dasl.SparseRangeSet

open Silmaril.Formats.Dasl.SparseRangeSet Silmaril.Formats.Dasl.SparseRangeSet.Interval

theorem covers_cons {head : Interval} {tail : List Interval} {point : Int} :
    Covers (head :: tail) point ↔ head.Includes point ∨ Covers tail point := by
  simp [Covers, List.mem_cons, or_and_right, exists_or]

private theorem before_trans {left mid right : Interval} (first : left.Before mid) (second : mid.Before right) :
    left.Before right := by
  have := mid.ordered
  unfold Before at *
  omega

private theorem includes_hull {left right : Interval} {point : Int}
    (first : ¬ left.Before right) (second : ¬ right.Before left) :
    (left.hull right).Includes point ↔ left.Includes point ∨ right.Includes point := by
  have := left.ordered
  have := right.ordered
  simp only [Includes, hull, Int64.toInt_ofIntLE, Before] at *
  omega

theorem covers_insert (newRange : Interval) (ranges : List Interval) (point : Int) :
    Covers (insertRange newRange ranges) point ↔ newRange.Includes point ∨ Covers ranges point := by
  induction ranges generalizing newRange with
  | nil => exact covers_cons
  | cons head tail ih =>
    simp only [insertRange]
    split
    · exact covers_cons
    · split
      · simp only [covers_cons, ih]; tauto
      · simp only [ih, covers_cons, includes_hull ‹¬ newRange.Before head› ‹¬ head.Before newRange›]; tauto

theorem covers_merge (ranges : List Interval) (point : Int) :
    Covers (mergeRanges ranges) point ↔ Covers ranges point := by
  induction ranges with
  | nil => rfl
  | cons head tail ih =>
    simp only [mergeRanges, List.foldr_cons] at ih ⊢
    rw [covers_insert, ih, covers_cons]

private theorem separated_insert (newRange : Interval) {ranges : List Interval}
    (separated : ranges.Pairwise Before) : (insertRange newRange ranges).Pairwise Before := by
  induction ranges generalizing newRange with
  | nil => simp [insertRange]
  | cons head tail ih =>
    obtain ⟨beforeTail, tailSeparated⟩ := List.pairwise_cons.mp separated
    simp only [insertRange]
    split
    next before =>
      refine List.pairwise_cons.mpr ⟨?_, separated⟩
      intro interval hit
      rcases List.mem_cons.mp hit with rfl | hit
      · exact before
      · exact before_trans before (beforeTail _ hit)
    next =>
      split
      next after =>
        refine List.pairwise_cons.mpr ⟨?_, ih newRange tailSeparated⟩
        intro interval hit
        have covered : Covers (insertRange newRange tail) interval.lower.toInt :=
          ⟨interval, hit, le_rfl, interval.ordered⟩
        rcases (covers_insert _ _ _).mp covered with ⟨lower, _⟩ | ⟨original, originalHit, lower, _⟩
        · exact lt_of_lt_of_le after lower
        · exact lt_of_lt_of_le (beforeTail original originalHit) lower
      next => exact ih _ tailSeparated

theorem merge_separated (ranges : List Interval) : (mergeRanges ranges).Pairwise Before := by
  induction ranges with
  | nil => exact List.Pairwise.nil
  | cons head tail ih => exact separated_insert head ih

private theorem tail_misses {head : Interval} {tail : List Interval} {point : Int}
    (separated : ∀ interval ∈ tail, head.Before interval) (below : point ≤ head.upper.toInt + 1) :
    ¬ Covers tail point := by
  rintro ⟨interval, hit, lower, _⟩
  exact (not_lt_of_ge (lower.trans below)) (separated interval hit)

private theorem lower_le {head : Interval} {tail : List Interval} {point : Int}
    (separated : ∀ interval ∈ tail, head.Before interval) (covered : Covers (head :: tail) point) :
    head.lower.toInt ≤ point := by
  rcases covers_cons.mp covered with ⟨lower, _⟩ | ⟨interval, hit, lower, _⟩
  · exact lower
  · have := head.ordered
    have after := separated interval hit
    unfold Before at after
    omega

private theorem upper_le {left right : Interval} {leftTail rightTail : List Interval}
    (separated : ∀ interval ∈ leftTail, left.Before interval) (sameLower : left.lower.toInt = right.lower.toInt)
    (included : ∀ point, Covers (right :: rightTail) point → Covers (left :: leftTail) point) :
    right.upper.toInt ≤ left.upper.toInt := by
  by_contra! shorter
  have inRight : Covers (right :: rightTail) (left.upper.toInt + 1) := by
    have := left.ordered
    exact covers_cons.mpr (Or.inl ⟨by omega, by omega⟩)
  rcases covers_cons.mp (included _ inRight) with ⟨_, upper⟩ | tailHit
  · omega
  · exact tail_misses separated le_rfl tailHit

theorem eq_of_covers {left right : List Interval} (leftSeparated : left.Pairwise Before)
    (rightSeparated : right.Pairwise Before) (same : ∀ point, Covers left point ↔ Covers right point) :
    left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons head tail =>
      have hit := (same head.lower.toInt).mpr ⟨head, by simp, le_rfl, head.ordered⟩
      simp [Covers] at hit
  | cons leftHead leftTail ih =>
    cases right with
    | nil =>
      have hit := (same leftHead.lower.toInt).mp ⟨leftHead, by simp, le_rfl, leftHead.ordered⟩
      simp [Covers] at hit
    | cons rightHead rightTail =>
      obtain ⟨leftBefore, leftRest⟩ := List.pairwise_cons.mp leftSeparated
      obtain ⟨rightBefore, rightRest⟩ := List.pairwise_cons.mp rightSeparated
      have sameLower : leftHead.lower.toInt = rightHead.lower.toInt := le_antisymm
        (lower_le leftBefore ((same _).mpr ⟨rightHead, by simp, le_rfl, rightHead.ordered⟩))
        (lower_le rightBefore ((same _).mp ⟨leftHead, by simp, le_rfl, leftHead.ordered⟩))
      have sameUpper : leftHead.upper.toInt = rightHead.upper.toInt := le_antisymm
        (upper_le rightBefore sameLower.symm fun point => (same point).mp)
        (upper_le leftBefore sameLower fun point => (same point).mpr)
      have sameHead : leftHead = rightHead := by
        cases leftHead; cases rightHead
        simp_all only [Int64.toInt_inj]
      subst rightHead
      congr 1
      apply ih leftRest rightRest
      intro point
      by_cases inHead : leftHead.Includes point
      · exact iff_of_false (tail_misses leftBefore (by have := inHead.2; omega))
          (tail_misses rightBefore (by have := inHead.2; omega))
      · simpa only [covers_cons, inHead, false_or] using same point

theorem mem_interval {interval : Interval} {key : Int64} : key ∈ interval.members ↔ interval.Includes key.toInt := by
  simp only [Interval.members, Finset.mem_map, Finset.mem_attach, true_and]
  constructor
  · rintro ⟨point, rfl⟩
    change interval.Includes (interval.key point).toInt
    simpa [Interval.key, Includes, wideMembers] using point.property
  · intro included
    exact ⟨⟨key.toInt, Finset.mem_Icc.mpr included⟩, Int64.ofIntLE_toInt key⟩

theorem mem_ranges (ranges : List Interval) (key : Int64) :
    key ∈ ranges.foldr (fun interval rest => interval.members ∪ rest) ∅ ↔ Covers ranges key.toInt := by
  induction ranges with
  | nil => simp [Covers]
  | cons head tail ih => simp only [List.foldr_cons, Finset.mem_union, mem_interval, ih, covers_cons]

theorem covers_iff_exists_member (layout : Layout) (point : Int) :
    Covers layout.ranges point ↔ ∃ key ∈ Formats.Dasl.SparseRangeSet.members layout, key.toInt = point := by
  simp only [Formats.Dasl.SparseRangeSet.members, mem_ranges]
  constructor
  · rintro ⟨interval, hit, lower, upper⟩
    let key := Int64.ofIntLE point (interval.lower.minValue_le_toInt.trans lower)
      (upper.trans interval.upper.toInt_le)
    refine ⟨key, ?_, by simp [key]⟩
    simpa only [key, Int64.toInt_ofIntLE] using (show Covers layout.ranges point from ⟨interval, hit, lower, upper⟩)
  · rintro ⟨key, hit, rfl⟩
    exact hit

theorem covers_singletons (keys : List Int64) (key : Int64) :
    Covers (keys.map Interval.singleton) key.toInt ↔ key ∈ keys := by
  simp only [Covers, List.mem_map, exists_exists_and_eq_and]
  simp [Interval.singleton, Includes, ← le_antisymm_iff, Int64.toInt_inj]

theorem card_ranges {ranges : List Interval} (separated : ranges.Pairwise Before) :
    (ranges.map Interval.cardinality).sum =
      (ranges.foldr (fun (interval : Interval) rest => interval.members ∪ rest) ∅).card := by
  induction ranges with
  | nil => rfl
  | cons head tail ih =>
    obtain ⟨before, tailSeparated⟩ := List.pairwise_cons.mp separated
    have disjoint : Disjoint head.members (tail.foldr (fun interval rest => interval.members ∪ rest) ∅) := by
      rw [Finset.disjoint_left]
      intro key inHead inTail
      have upper := (mem_interval.mp inHead).2
      exact tail_misses before (by omega) ((mem_ranges _ _).mp inTail)
    rw [List.map_cons, List.sum_cons, List.foldr_cons, Finset.card_union_of_disjoint disjoint, ih tailSeparated]
    simp [Interval.cardinality, Interval.members, Interval.wideMembers, Int.card_Icc]

end Silmaril.Proofs.Formats.Dasl.SparseRangeSet
