module

public import Silmaril.Numeric.TimeZone.Defs
import Silmaril.Proofs.Numeric.TimeZone.Rules

public section

namespace Silmaril.Proofs.Numeric.TimeZone

open Silmaril.Numeric.TimeZone

theorem resolveUnique_eq_some_iff {rules : Rules} {wall : WallTime} {time : UnixTime} :
    rules.resolve? wall .unique = some time ↔
      rules.Matches wall time ∧ ∀ other, rules.Matches wall other → other = time := by
  simp only [← mem_candidates_iff, Rules.resolve?]
  have sorted := candidates_pairwise rules wall
  cases candidateEq : rules.candidates wall with
  | nil => simp
  | cons first tail =>
    cases tail with
    | nil => simp [eq_comm]
    | cons second rest =>
      simp only [reduceCtorEq, false_iff]
      rintro ⟨_, unique⟩
      have firstEq := unique first (by simp)
      have secondEq := unique second (by simp)
      rw [candidateEq] at sorted
      have lt := (List.pairwise_cons.mp sorted).1 second (by simp)
      rw [firstEq, secondEq] at lt
      exact Int.lt_irrefl _ lt

private theorem head_rel {times : List UnixTime} {first time : UnixTime}
    {rel : UnixTime → UnixTime → Prop} (refl : ∀ a, rel a a) (sorted : times.Pairwise rel)
    (head : times.head? = some first) (member : time ∈ times) : rel first time := by
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp head
  rcases List.mem_cons.mp member with rfl | member
  · exact refl _
  · exact (List.pairwise_cons.mp sorted).1 _ member

theorem resolveEarliest_spec {rules : Rules} {wall : WallTime} {time : UnixTime}
    (resolved : rules.resolve? wall .earliest = some time) :
    rules.Matches wall time ∧ ∀ other, rules.Matches wall other → time.ticks ≤ other.ticks := by
  have sorted := (candidates_pairwise rules wall).imp (fun h => Int.le_of_lt h)
  exact ⟨mem_candidates_iff.mp (List.mem_of_head? resolved),
    fun _ h => head_rel (fun _ => Int.le_refl _) sorted resolved (mem_candidates_iff.mpr h)⟩

theorem resolveLatest_spec {rules : Rules} {wall : WallTime} {time : UnixTime}
    (resolved : rules.resolve? wall .latest = some time) :
    rules.Matches wall time ∧ ∀ other, rules.Matches wall other → other.ticks ≤ time.ticks := by
  have sorted := (List.pairwise_reverse.mpr (candidates_pairwise rules wall)).imp
    (fun h => Int.le_of_lt h)
  have head : (rules.candidates wall).reverse.head? = some time := by
    simpa only [List.head?_reverse, Rules.resolve?] using resolved
  have bound {other : UnixTime} (h : rules.Matches wall other) : other.ticks ≤ time.ticks := by
    have member : other ∈ (rules.candidates wall).reverse :=
      List.mem_reverse.mpr (mem_candidates_iff.mpr h)
    exact head_rel (fun _ => Int.le_refl _) sorted head member
  exact ⟨mem_candidates_iff.mp (List.mem_of_getLast? resolved), fun _ h => bound h⟩

private theorem offset_bounds {rules : Rules} {lower upper : Int}
    (bounded : rules.OffsetsWithin lower upper)
    {time : UnixTime} {offset : Offset} (actual : rules.offsetAt? time = some offset) :
    lower ≤ offset.nanoseconds ∧ offset.nanoseconds ≤ upper := by
  cases rules with
  | fixed fixedOffset =>
    have eq : fixedOffset = offset := Option.some.inj actual
    simpa only [Rules.OffsetsWithin, ← eq] using bounded
  | scheduled schedule =>
    obtain ⟨segment, member, _, rfl⟩ := offsetAt_eq_some_iff.mp actual
    exact bounded segment member

theorem sameTime_discrepancy {left right : Rules} {time : UnixTime}
    {leftOffset rightOffset : Offset} {leftWall rightWall : WallTime}
    (leftActual : left.offsetAt? time = some leftOffset)
    (rightActual : right.offsetAt? time = some rightOffset)
    (leftReading : left.toLocal? time = some leftWall)
    (rightReading : right.toLocal? time = some rightWall) :
    leftWall.ticks - rightWall.ticks = leftOffset.nanoseconds - rightOffset.nanoseconds := by
  simp only [Rules.toLocal?, leftActual, rightActual, Option.map_some, Option.some.injEq]
    at leftReading rightReading
  rw [← leftReading, ← rightReading]
  simp only [Offset.toLocal]
  omega

theorem sameTime_discrepancy_bound {left right : Rules} {time : UnixTime}
    {leftWall rightWall : WallTime} {lower upper : Int}
    (leftBound : left.OffsetsWithin lower upper) (rightBound : right.OffsetsWithin lower upper)
    (leftReading : left.toLocal? time = some leftWall)
    (rightReading : right.toLocal? time = some rightWall) :
    lower - upper ≤ leftWall.ticks - rightWall.ticks ∧
      leftWall.ticks - rightWall.ticks ≤ upper - lower := by
  obtain ⟨leftOffset, leftActual, _⟩ := Option.map_eq_some_iff.mp leftReading
  obtain ⟨rightOffset, rightActual, _⟩ := Option.map_eq_some_iff.mp rightReading
  have ⟨leftLow, leftHigh⟩ := offset_bounds leftBound leftActual
  have ⟨rightLow, rightHigh⟩ := offset_bounds rightBound rightActual
  rw [sameTime_discrepancy leftActual rightActual leftReading rightReading]
  omega

theorem candidate_spread_bound {rules : Rules} {wall : WallTime} {first second : UnixTime}
    {lower upper : Int} (bounded : rules.OffsetsWithin lower upper)
    (firstMatches : rules.Matches wall first) (secondMatches : rules.Matches wall second) :
    lower - upper ≤ second.ticks - first.ticks ∧ second.ticks - first.ticks ≤ upper - lower := by
  obtain ⟨firstOffset, firstActual, firstWall⟩ := Option.map_eq_some_iff.mp firstMatches
  obtain ⟨secondOffset, secondActual, secondWall⟩ := Option.map_eq_some_iff.mp secondMatches
  have ⟨firstLow, firstHigh⟩ := offset_bounds bounded firstActual
  have ⟨secondLow, secondHigh⟩ := offset_bounds bounded secondActual
  have wallEq := congrArg Numeric.Timestamp.Ticks.ticks (firstWall.trans secondWall.symm)
  simp only [Offset.toLocal] at wallEq
  omega

end Silmaril.Proofs.Numeric.TimeZone
