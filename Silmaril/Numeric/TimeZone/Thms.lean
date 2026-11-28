module

public import Silmaril.Numeric.TimeZone.Defs
import Silmaril.Proofs.Numeric.TimeZone.Civil
import Silmaril.Proofs.Numeric.TimeZone.Resolution
import Silmaril.Proofs.Numeric.TimeZone.Rules

/-! # Support, inverse candidates and bounds for time zone rules -/

public section

namespace Silmaril.Numeric.TimeZone

namespace Offset

@[simp] theorem fromLocal_toLocal (offset : Offset) (time : UnixTime) :
    offset.fromLocal (offset.toLocal time) = time :=
  Proofs.Numeric.TimeZone.fromLocal_toLocal offset time

@[simp] theorem toLocal_fromLocal (offset : Offset) (wall : WallTime) :
    offset.toLocal (offset.fromLocal wall) = wall :=
  Proofs.Numeric.TimeZone.toLocal_fromLocal offset wall

end Offset

namespace CivilReading

@[simp] theorem toWall_ofWall (wall : WallTime) : (ofWall wall).toWall? = some wall :=
  Proofs.Numeric.TimeZone.toWall_ofWall wall

theorem ofWall_toWall {civil : CivilReading} {wall : WallTime}
    (h : civil.toWall? = some wall) : ofWall wall = civil :=
  Proofs.Numeric.TimeZone.ofWall_toWall h

end CivilReading

namespace Segment

/-- A segment contributes at most one preimage, obtained by subtracting its offset. -/
theorem candidate_eq_some_iff {segment : Segment} {wall : WallTime} {time : UnixTime} :
    segment.candidate? wall = some time ↔
      segment.Contains time ∧ segment.offset.toLocal time = wall :=
  Proofs.Numeric.TimeZone.candidate_eq_some_iff

theorem translated_contains_iff {segment : Segment} {wall : WallTime} :
    segment.ContainsWall wall ↔ segment.Contains (segment.offset.fromLocal wall) :=
  Proofs.Numeric.TimeZone.translated_contains_iff

/-- Between the translated outer endpoints, an adjacent pair leaves exactly the
    half-open jump interval uncovered. The interval is nonempty for an offset increase. -/
theorem transition_gap_iff {before after : Segment} {wall : WallTime}
    (adjacent : before.stop = after.start)
    (left : (before.offset.toLocal before.start).ticks ≤ wall.ticks)
    (right : wall.ticks < (after.offset.toLocal after.stop).ticks) :
    (¬ before.ContainsWall wall ∧ ¬ after.ContainsWall wall) ↔
      (before.offset.toLocal before.stop).ticks ≤ wall.ticks ∧
        wall.ticks < (after.offset.toLocal before.stop).ticks :=
  Proofs.Numeric.TimeZone.transition_gap_iff adjacent left right

/-- The adjacent pair has two preimages exactly in the half-open fold interval.
    The outer endpoints clip the fold when either segment is short. -/
theorem transition_fold_iff {before after : Segment} {wall : WallTime}
    (adjacent : before.stop = after.start) :
    (before.ContainsWall wall ∧ after.ContainsWall wall) ↔
      max (before.offset.toLocal before.start).ticks (after.offset.toLocal before.stop).ticks ≤
        wall.ticks ∧
      wall.ticks <
        min (before.offset.toLocal before.stop).ticks (after.offset.toLocal after.stop).ticks :=
  Proofs.Numeric.TimeZone.transition_fold_iff adjacent

end Segment

namespace Schedule

/-- The segments cover exactly the stated support. -/
theorem contains_segment_iff {schedule : Schedule} {time : UnixTime} :
    (∃ segment ∈ schedule.segments, segment.Contains time) ↔ schedule.Supports time :=
  Proofs.Numeric.TimeZone.contains_segment_iff

/-- Every supported nominal instant belongs to just one segment. -/
theorem segment_unique {schedule : Schedule} {time : UnixTime} {first second : Segment}
    (firstMember : first ∈ schedule.segments) (secondMember : second ∈ schedule.segments)
    (firstContains : first.Contains time) (secondContains : second.Contains time) :
    first = second :=
  Proofs.Numeric.TimeZone.segment_unique firstMember secondMember firstContains secondContains

/-- The schedule uses the offset of the segment covering the input. -/
theorem offsetAt_eq_some_iff {schedule : Schedule} {time : UnixTime} {offset : Offset} :
    schedule.offsetAt? time = some offset ↔
      ∃ segment ∈ schedule.segments, segment.Contains time ∧ segment.offset = offset :=
  Proofs.Numeric.TimeZone.offsetAt_eq_some_iff

end Schedule

namespace Rules

/-- Offset lookup succeeds exactly on the rule's support. -/
theorem offsetAt_isSome_iff {rules : Rules} {time : UnixTime} :
    (rules.offsetAt? time).isSome = true ↔ rules.Supports time :=
  Proofs.Numeric.TimeZone.offsetAt_isSome_iff

theorem toLocal_isSome_iff {rules : Rules} {time : UnixTime} :
    (rules.toLocal? time).isSome = true ↔ rules.Supports time := by
  simpa only [toLocal?, Option.isSome_map] using (offsetAt_isSome_iff (rules := rules) (time := time))

@[simp] theorem civilCandidates_ofWall (rules : Rules) (wall : WallTime) :
    rules.civilCandidates? (CivilReading.ofWall wall) = some (rules.candidates wall) := by
  simp [civilCandidates?]

/-- Candidate enumeration is sound and complete for the forward relation. -/
theorem mem_candidates_iff {rules : Rules} {wall : WallTime} {time : UnixTime} :
    time ∈ rules.candidates wall ↔ rules.Matches wall time :=
  Proofs.Numeric.TimeZone.mem_candidates_iff

/-- The candidate list is sorted in strictly increasing nominal Unix order. -/
theorem candidates_pairwise (rules : Rules) (wall : WallTime) :
    (rules.candidates wall).Pairwise (fun first second => first.ticks < second.ticks) :=
  Proofs.Numeric.TimeZone.candidates_pairwise rules wall

/-- The exact global candidate count is the number of translated segments covering the wall
    reading. Zero gives no preimage, one gives uniqueness and larger counts give folds. -/
theorem scheduled_candidates_length (schedule : Schedule) (wall : WallTime) :
    ((scheduled schedule).candidates wall).length =
      (schedule.segments.filter (fun segment => decide (segment.ContainsWall wall))).length :=
  Proofs.Numeric.TimeZone.scheduled_candidates_length schedule wall

theorem resolveUnique_eq_some_iff {rules : Rules} {wall : WallTime} {time : UnixTime} :
    rules.resolve? wall .unique = some time ↔
      rules.Matches wall time ∧ ∀ other, rules.Matches wall other → other = time :=
  Proofs.Numeric.TimeZone.resolveUnique_eq_some_iff

theorem resolveEarliest_spec {rules : Rules} {wall : WallTime} {time : UnixTime}
    (resolved : rules.resolve? wall .earliest = some time) :
    rules.Matches wall time ∧ ∀ other, rules.Matches wall other → time.ticks ≤ other.ticks :=
  Proofs.Numeric.TimeZone.resolveEarliest_spec resolved

theorem resolveLatest_spec {rules : Rules} {wall : WallTime} {time : UnixTime}
    (resolved : rules.resolve? wall .latest = some time) :
    rules.Matches wall time ∧ ∀ other, rules.Matches wall other → other.ticks ≤ time.ticks :=
  Proofs.Numeric.TimeZone.resolveLatest_spec resolved

theorem resolveEarliest_eq_none_iff {rules : Rules} {wall : WallTime} :
    rules.resolve? wall .earliest = none ↔ ∀ time, ¬ rules.Matches wall time := by
  simp only [resolve?, List.head?_eq_none_iff, List.eq_nil_iff_forall_not_mem, mem_candidates_iff]

theorem resolveLatest_eq_none_iff {rules : Rules} {wall : WallTime} :
    rules.resolve? wall .latest = none ↔ ∀ time, ¬ rules.Matches wall time := by
  simp only [resolve?, List.getLast?_eq_none_iff, List.eq_nil_iff_forall_not_mem, mem_candidates_iff]

/-- At a shared nominal instant, the difference of two wall readings is the difference
    of the active offsets. -/
theorem sameTime_discrepancy {left right : Rules} {time : UnixTime}
    {leftOffset rightOffset : Offset} {leftWall rightWall : WallTime}
    (leftActual : left.offsetAt? time = some leftOffset)
    (rightActual : right.offsetAt? time = some rightOffset)
    (leftReading : left.toLocal? time = some leftWall)
    (rightReading : right.toLocal? time = some rightWall) :
    leftWall.ticks - rightWall.ticks = leftOffset.nanoseconds - rightOffset.nanoseconds :=
  Proofs.Numeric.TimeZone.sameTime_discrepancy leftActual rightActual leftReading rightReading

theorem sameTime_discrepancy_bound {left right : Rules} {time : UnixTime}
    {leftWall rightWall : WallTime} {lower upper : Int}
    (leftBound : left.OffsetsWithin lower upper) (rightBound : right.OffsetsWithin lower upper)
    (leftReading : left.toLocal? time = some leftWall)
    (rightReading : right.toLocal? time = some rightWall) :
    lower - upper ≤ leftWall.ticks - rightWall.ticks ∧
      leftWall.ticks - rightWall.ticks ≤ upper - lower :=
  Proofs.Numeric.TimeZone.sameTime_discrepancy_bound leftBound rightBound leftReading rightReading

/-- Any two nominal preimages of one wall reading differ by at most the offset range width. -/
theorem candidate_spread_bound {rules : Rules} {wall : WallTime} {first second : UnixTime}
    {lower upper : Int} (bounded : rules.OffsetsWithin lower upper)
    (firstMatches : rules.Matches wall first) (secondMatches : rules.Matches wall second) :
    lower - upper ≤ second.ticks - first.ticks ∧ second.ticks - first.ticks ≤ upper - lower :=
  Proofs.Numeric.TimeZone.candidate_spread_bound bounded firstMatches secondMatches

/-- The earliest and latest policies agree within the same offset range width. -/
theorem resolver_spread_bound {rules : Rules} {wall : WallTime} {first last : UnixTime}
    {lower upper : Int} (bounded : rules.OffsetsWithin lower upper)
    (earliest : rules.resolve? wall .earliest = some first)
    (latest : rules.resolve? wall .latest = some last) :
    first.ticks ≤ last.ticks ∧ last.ticks - first.ticks ≤ upper - lower := by
  have lastMatches := (resolveLatest_spec latest).1
  exact ⟨(resolveEarliest_spec earliest).2 _ lastMatches,
    (candidate_spread_bound bounded (resolveEarliest_spec earliest).1 lastMatches).2⟩

end Rules
end Silmaril.Numeric.TimeZone
