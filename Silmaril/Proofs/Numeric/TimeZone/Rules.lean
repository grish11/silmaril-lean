module

public import Silmaril.Numeric.TimeZone.Defs

public section

namespace Silmaril.Proofs.Numeric.TimeZone

open Silmaril.Numeric.TimeZone

theorem fromLocal_toLocal (offset : Offset) (time : UnixTime) :
    offset.fromLocal (offset.toLocal time) = time := by
  cases time
  simp [Offset.fromLocal, Offset.toLocal]

theorem toLocal_fromLocal (offset : Offset) (wall : WallTime) :
    offset.toLocal (offset.fromLocal wall) = wall := by
  cases wall
  simp [Offset.fromLocal, Offset.toLocal]

theorem candidate_eq_some_iff {segment : Segment} {wall : WallTime} {time : UnixTime} :
    segment.candidate? wall = some time ↔
      segment.Contains time ∧ segment.offset.toLocal time = wall := by
  by_cases h : segment.Contains (segment.offset.fromLocal wall)
  · rw [Segment.candidate?, ite_eq_left h, Option.some.injEq]
    constructor
    · rintro rfl
      exact ⟨h, toLocal_fromLocal _ _⟩
    · rintro ⟨_, rfl⟩
      exact fromLocal_toLocal _ _
  · rw [Segment.candidate?, ite_eq_right h]
    simp only [reduceCtorEq, false_iff]
    rintro ⟨ht, rfl⟩
    exact h (by simpa only [fromLocal_toLocal] using ht)

theorem translated_contains_iff {segment : Segment} {wall : WallTime} :
    segment.ContainsWall wall ↔ segment.Contains (segment.offset.fromLocal wall) := by
  simp only [Segment.ContainsWall, Segment.Contains, Offset.toLocal, Offset.fromLocal]
  omega

theorem transition_gap_iff {before after : Segment} {wall : WallTime}
    (adjacent : before.stop = after.start)
    (left : (before.offset.toLocal before.start).ticks ≤ wall.ticks)
    (right : wall.ticks < (after.offset.toLocal after.stop).ticks) :
    (¬ before.ContainsWall wall ∧ ¬ after.ContainsWall wall) ↔
      (before.offset.toLocal before.stop).ticks ≤ wall.ticks ∧
        wall.ticks < (after.offset.toLocal before.stop).ticks := by
  simp only [Segment.ContainsWall, ← adjacent]
  omega

theorem transition_fold_iff {before after : Segment} {wall : WallTime}
    (adjacent : before.stop = after.start) :
    (before.ContainsWall wall ∧ after.ContainsWall wall) ↔
      max (before.offset.toLocal before.start).ticks (after.offset.toLocal before.stop).ticks ≤
        wall.ticks ∧
      wall.ticks <
        min (before.offset.toLocal before.stop).ticks (after.offset.toLocal after.stop).ticks := by
  simp only [Segment.ContainsWall, ← adjacent, max_le_iff, lt_min_iff]
  omega

open Schedule.Internal (segmentsFrom)

private theorem ordered_endpoints {start stop : UnixTime} {transitions : List Transition}
    (ordered : Schedule.Ordered start stop transitions) : start.ticks < stop.ticks := by
  induction transitions generalizing start with
  | nil => exact ordered
  | cons _ _ ih => exact Int.lt_trans ordered.1 (ih ordered.2)

private theorem segment_bounds {start stop : UnixTime} {offset : Offset}
    {transitions : List Transition} (ordered : Schedule.Ordered start stop transitions)
    {segment : Segment} (member : segment ∈ segmentsFrom start stop offset transitions) :
    start.ticks ≤ segment.start.ticks ∧ segment.start.ticks < segment.stop.ticks ∧
      segment.stop.ticks ≤ stop.ticks := by
  induction transitions generalizing start offset with
  | nil =>
    rw [segmentsFrom, List.mem_singleton] at member
    subst segment
    exact ⟨Int.le_refl _, ordered, Int.le_refl _⟩
  | cons transition rest ih =>
    have ⟨step, tail⟩ := ordered
    rw [segmentsFrom, List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨Int.le_refl _, step, Int.le_of_lt (ordered_endpoints tail)⟩
    · have ⟨lower, nonempty, upper⟩ := ih tail member
      exact ⟨by omega, nonempty, upper⟩

private theorem segments_cover {start stop time : UnixTime} {offset : Offset}
    {transitions : List Transition} (ordered : Schedule.Ordered start stop transitions)
    (lower : start.ticks ≤ time.ticks) (upper : time.ticks < stop.ticks) :
    ∃ segment ∈ segmentsFrom start stop offset transitions, segment.Contains time := by
  induction transitions generalizing start offset with
  | nil => exact ⟨⟨start, stop, offset⟩, by simp [segmentsFrom], lower, upper⟩
  | cons transition rest ih =>
    rw [segmentsFrom]
    by_cases h : time.ticks < transition.instant.ticks
    · exact ⟨⟨start, transition.instant, offset⟩, List.mem_cons_self, lower, h⟩
    · have ⟨segment, member, contains⟩ := ih (offset := transition.offsetAfter) ordered.2 (by omega)
      exact ⟨segment, List.mem_cons_of_mem _ member, contains⟩

private theorem segments_pairwise {start stop : UnixTime} {offset : Offset}
    {transitions : List Transition} (ordered : Schedule.Ordered start stop transitions) :
    (segmentsFrom start stop offset transitions).Pairwise
      (fun first second => first.stop.ticks ≤ second.start.ticks) := by
  induction transitions generalizing start offset with
  | nil => simp [segmentsFrom]
  | cons transition rest ih =>
    rw [segmentsFrom, List.pairwise_cons]
    exact ⟨fun _ member => (segment_bounds ordered.2 member).1, ih ordered.2⟩

theorem contains_segment_iff {schedule : Schedule} {time : UnixTime} :
    (∃ segment ∈ schedule.segments, segment.Contains time) ↔ schedule.Supports time := by
  constructor
  · rintro ⟨segment, member, h⟩
    have ⟨lower, _, upper⟩ := segment_bounds schedule.ordered member
    exact ⟨Int.le_trans lower h.1, Int.lt_of_lt_of_le h.2 upper⟩
  · rintro ⟨lower, upper⟩
    exact segments_cover schedule.ordered lower upper

private theorem contains_unique {segments : List Segment} {first second : Segment}
    {time : UnixTime} (ordered : segments.Pairwise
      (fun left right => left.stop.ticks ≤ right.start.ticks))
    (firstMember : first ∈ segments) (secondMember : second ∈ segments)
    (firstContains : first.Contains time) (secondContains : second.Contains time) :
    first = second := by
  induction segments with
  | nil => simp at firstMember
  | cons head tail ih =>
    rw [List.pairwise_cons] at ordered
    rw [List.mem_cons] at firstMember secondMember
    rcases firstMember with rfl | hFirst <;> rcases secondMember with rfl | hSecond
    · rfl
    · have separated := ordered.1 _ hSecond
      have firstUpper := firstContains.2
      have secondLower := secondContains.1
      omega
    · have separated := ordered.1 _ hFirst
      have secondUpper := secondContains.2
      have firstLower := firstContains.1
      omega
    · exact ih ordered.2 hFirst hSecond

theorem segment_unique {schedule : Schedule} {time : UnixTime} {first second : Segment}
    (firstMember : first ∈ schedule.segments) (secondMember : second ∈ schedule.segments)
    (firstContains : first.Contains time) (secondContains : second.Contains time) :
    first = second :=
  contains_unique (segments_pairwise schedule.ordered)
    firstMember secondMember firstContains secondContains

theorem offsetAt_eq_some_iff {schedule : Schedule} {time : UnixTime} {offset : Offset} :
    schedule.offsetAt? time = some offset ↔
      ∃ segment ∈ schedule.segments, segment.Contains time ∧ segment.offset = offset := by
  have found {result : Offset} (h : schedule.offsetAt? time = some result) :
      ∃ segment ∈ schedule.segments, segment.Contains time ∧ segment.offset = result := by
    obtain ⟨earlier, segment, later, listEq, h, _⟩ := List.findSome?_eq_some_iff.mp h
    change (if segment.Contains time then some segment.offset else none) = some result at h
    split at h
    next contains => exact ⟨segment, by simp [listEq], contains, Option.some.inj h⟩
    next => contradiction
  refine ⟨found, ?_⟩
  rintro ⟨segment, member, contains, rfl⟩
  cases result : schedule.offsetAt? time with
  | none =>
    have h := List.findSome?_eq_none_iff.mp result segment member
    change (if segment.Contains time then some segment.offset else none) = none at h
    simp [contains] at h
  | some offset =>
    obtain ⟨other, otherMember, otherContains, rfl⟩ := found result
    have eq := segment_unique member otherMember contains otherContains
    rw [eq]

theorem offsetAt_isSome_iff {rules : Rules} {time : UnixTime} :
    (rules.offsetAt? time).isSome = true ↔ rules.Supports time := by
  cases rules with
  | fixed offset => simp [Rules.offsetAt?, Rules.Supports]
  | scheduled schedule =>
    rw [Rules.offsetAt?, Rules.Supports, ← contains_segment_iff]
    constructor
    · intro h
      obtain ⟨offset, h⟩ := Option.isSome_iff_exists.mp h
      obtain ⟨segment, member, contains, _⟩ := offsetAt_eq_some_iff.mp h
      exact ⟨segment, member, contains⟩
    · rintro ⟨segment, member, contains⟩
      exact Option.isSome_iff_exists.mpr ⟨_, offsetAt_eq_some_iff.mpr
        ⟨segment, member, contains, rfl⟩⟩

theorem mem_candidates_iff {rules : Rules} {wall : WallTime} {time : UnixTime} :
    time ∈ rules.candidates wall ↔ rules.Matches wall time := by
  cases rules with
  | fixed offset =>
    simp only [Rules.candidates, List.mem_singleton, Rules.Matches, Rules.toLocal?,
      Rules.offsetAt?, Option.map_some, Option.some.injEq]
    constructor <;> rintro rfl
    · exact toLocal_fromLocal _ _
    · exact (fromLocal_toLocal _ _).symm
  | scheduled schedule =>
    simp only [Rules.candidates, List.mem_filterMap, candidate_eq_some_iff,
      Rules.Matches, Rules.toLocal?, Rules.offsetAt?, Option.map_eq_some_iff,
      offsetAt_eq_some_iff]
    constructor
    · rintro ⟨segment, member, contains, rfl⟩
      exact ⟨segment.offset, ⟨segment, member, contains, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨segment, member, contains, rfl⟩, wallEq⟩
      exact ⟨segment, member, contains, wallEq⟩

theorem candidates_pairwise (rules : Rules) (wall : WallTime) :
    (rules.candidates wall).Pairwise (fun first second => first.ticks < second.ticks) := by
  cases rules with
  | fixed offset => simp [Rules.candidates]
  | scheduled schedule =>
    rw [Rules.candidates, List.pairwise_filterMap]
    apply (segments_pairwise schedule.ordered).imp
    intro before after separated first hFirst second hSecond
    have firstBound := (candidate_eq_some_iff.mp hFirst).1.2
    have secondBound := (candidate_eq_some_iff.mp hSecond).1.1
    omega

private theorem count_translated (segments : List Segment) (wall : WallTime) :
    (segments.filterMap (·.candidate? wall)).length =
      (segments.filter (fun segment => decide
        (segment.Contains (segment.offset.fromLocal wall)))).length := by
  induction segments with
  | nil => rfl
  | cons segment tail ih =>
    simp only [Segment.candidate?] at ih ⊢
    by_cases h : segment.Contains (segment.offset.fromLocal wall) <;> simp [h, ih]

theorem scheduled_candidates_length (schedule : Schedule) (wall : WallTime) :
    ((Rules.scheduled schedule).candidates wall).length =
      (schedule.segments.filter (fun segment => decide
        (segment.ContainsWall wall))).length := by
  simp only [Rules.candidates, translated_contains_iff]
  exact count_translated _ _

end Silmaril.Proofs.Numeric.TimeZone
