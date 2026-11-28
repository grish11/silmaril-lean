module

public import Silmaril.Semantics.TrackA.Concurrency.Defs
import Silmaril.Proofs.Semantics.TrackA.Concurrency.Machine
import Mathlib.Data.List.Induction

@[expose] public section

namespace Silmaril.Proofs.Semantics.TrackA.Concurrency

open Silmaril.Semantics.TrackA.Concurrency

variable {T L R : Type} [DecidableEq T] [DecidableEq L] [DecidableEq R]
variable {profile : RaceProfile} {xs ys : List (Event T L R)} {i j : Nat}

theorem direct_lt (edge : direct profile xs i j = true) : i < j := by
  unfold direct at edge
  split at edge <;> simp_all

private theorem hb_saturated {fuel fuel' : Nat} (bound : j < fuel) (bound' : j < fuel') :
    happensBeforeWithin profile xs i fuel j = happensBeforeWithin profile xs i fuel' j := by
  induction j using Nat.strong_induction_on generalizing fuel fuel' with
  | ind j ih =>
    cases fuel with
    | zero => omega
    | succ n =>
      cases fuel' with
      | zero => omega
      | succ n' =>
        simp only [happensBeforeWithin]
        congr 1
        apply List.any_congr rfl
        intro k
        by_cases lt : k < j
        · rw [ite_eq_left lt, ite_eq_left lt, ih k lt (fuel := n) (fuel' := n') (by omega) (by omega)]
        · simp [lt]

private theorem hb_step :
    happensBefore profile xs i j = true ↔
      direct profile xs i j = true ∨
        ∃ k, k < j ∧ happensBefore profile xs i k = true ∧ direct profile xs k j = true := by
  unfold happensBefore
  rw [happensBeforeWithin]
  simp only [Bool.or_eq_true, List.any_eq_true, List.mem_range]
  apply or_congr Iff.rfl
  apply exists_congr
  intro k
  apply and_congr_right
  intro lt
  rw [ite_eq_left lt, hb_saturated (j := k) lt (Nat.lt_succ_self k), Bool.and_eq_true]

theorem happensBefore_iff_transGen :
    happensBefore profile xs i j = true ↔ Relation.TransGen (fun a b => direct profile xs a b = true) i j := by
  constructor
  · induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hb
      rcases hb_step.mp hb with edge | ⟨mid, lt, prev, edge⟩
      · exact .single edge
      · exact .tail (ih mid lt prev) edge
  · intro path
    induction path with
    | single edge => exact hb_step.mpr (.inl edge)
    | @tail mid j _ edge ih => exact hb_step.mpr (.inr ⟨mid, direct_lt edge, ih, edge⟩)

theorem happensBefore_lt (hb : happensBefore profile xs i j = true) : i < j := by
  have path := happensBefore_iff_transGen.mp hb
  clear hb
  induction path with
  | single edge => exact direct_lt edge
  | tail _ edge ih => exact Nat.lt_trans ih (direct_lt edge)

private theorem direct_append :
    j < xs.length → direct profile (xs ++ ys) i j = direct profile xs i j := by
  intro jBound
  unfold direct
  split
  next lt =>
    rw [List.getElem?_append_left (Nat.lt_trans lt jBound), List.getElem?_append_left jBound]
    cases xs[i]? with
    | none => rfl
    | some a =>
      cases xs[j]? with
      | none => rfl
      | some b =>
        cases profile with
        | mutexOnly => rfl
        | mixed =>
          cases a.action <;> cases b.action <;>
            simp only [atomicSync, List.take_append_of_le_length (Nat.le_of_lt jBound)]
  next => rfl

theorem happensBefore_append (bound : j < xs.length) :
    happensBefore profile (xs ++ ys) i j = happensBefore profile xs i j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    apply Bool.eq_iff_iff.mpr
    rw [hb_step (xs := xs ++ ys), hb_step (xs := xs)]
    simp only [direct_append bound]
    constructor
    · rintro (edge | ⟨k, lt, path, edge⟩)
      · exact .inl edge
      · exact .inr ⟨k, lt, ih k lt (Nat.lt_trans lt bound) ▸ path, edge⟩
    · rintro (edge | ⟨k, lt, path, edge⟩)
      · exact .inl edge
      · exact .inr ⟨k, lt, (ih k lt (Nat.lt_trans lt bound)).symm ▸ path, edge⟩

theorem hasRace_iff :
    hasRace profile xs = true ↔ ∃ i j, i < j ∧ j < xs.length ∧ racePair profile xs i j = true := by
  simp only [hasRace, List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨j, jBound, i, lt, race⟩
    exact ⟨i, j, lt, jBound, race⟩
  · rintro ⟨i, j, lt, jBound, race⟩
    exact ⟨j, jBound, i, lt, race⟩

theorem hasRace_append (race : hasRace profile xs = true) : hasRace profile (xs ++ ys) = true := by
  obtain ⟨i, j, lt, bound, pair⟩ := hasRace_iff.mp race
  apply hasRace_iff.mpr
  refine ⟨i, j, lt, by simp only [List.length_append]; omega, ?_⟩
  unfold racePair at pair ⊢
  simpa only [ite_eq_left lt, List.getElem?_append_left (Nat.lt_trans lt bound),
    List.getElem?_append_left bound, happensBefore_append bound] using pair

private theorem direct_mixed (edge : direct .mutexOnly xs i j = true) :
    direct .mixed xs i j = true := by
  have lt := direct_lt edge
  simp only [direct, ite_eq_left lt] at edge ⊢
  cases first : xs[i]? <;> cases second : xs[j]? <;> simp_all

theorem happensBefore_mixed (hb : happensBefore .mutexOnly xs i j = true) :
    happensBefore .mixed xs i j = true :=
  happensBefore_iff_transGen.mpr
    (Relation.TransGen.mono (fun a b => direct_mixed (xs := xs) (i := a) (j := b))
      i j (happensBefore_iff_transGen.mp hb))

theorem hasRace_mutexOnly_of_mixed (race : hasRace .mixed xs = true) :
    hasRace .mutexOnly xs = true := by
  obtain ⟨i, j, lt, bound, pair⟩ := hasRace_iff.mp race
  apply hasRace_iff.mpr
  refine ⟨i, j, lt, bound, ?_⟩
  unfold racePair at pair ⊢
  simp only [ite_eq_left lt] at pair ⊢
  cases first : xs[i]? <;> cases second : xs[j]? <;> simp [first, second] at pair ⊢
  refine ⟨pair.1.1, Bool.eq_false_iff.mpr fun hb => ?_⟩
  have ordered := happensBefore_mixed (xs := xs) (i := i) (j := j) hb
  simp [pair.1.2] at ordered

variable {start finish : Config T L R}

theorem classifyHistory_eq_some_iff {result : RaceClass} :
    classifyHistory profile start xs = some result ↔
      ∃ finish, ClassifiedRun profile start xs finish result := by
  unfold classifyHistory
  constructor
  · cases h : replay start (xs.map Event.thread) with
    | none => simp
    | some out =>
      obtain ⟨actual, finish⟩ := out
      by_cases labels : actual = xs
      · subst actual
        intro classified
        exact ⟨finish, (replay_iff.mp h).1, by simpa using classified⟩
      · simp [labels]
  · rintro ⟨finish, run, classified⟩
    rw [replay_iff.mpr ⟨run, rfl⟩]
    simp [classified]

theorem guarded_iff :
    GuardedRun profile start xs finish ↔ sc.MTr start xs finish ∧ RaceFree profile xs := by
  constructor
  · intro run
    induction run with
    | nil => exact ⟨.refl, rfl⟩
    | snoc _ step clean ih => exact ⟨Cslib.LTS.MTr.stepR sc ih.1 step, clean⟩
  · rintro ⟨run, clean⟩
    induction xs using List.reverseRecOn generalizing finish with
    | nil =>
      cases run
      exact .nil
    | append_singleton xs event ih =>
      obtain ⟨mid, prefixRun, lastRun⟩ := run.split
      have prefixClean : RaceFree profile xs := by
        apply Bool.eq_false_iff.mpr
        intro bad
        have := hasRace_append (ys := [event]) bad
        simp [clean] at this
      exact .snoc (ih prefixRun prefixClean) (Cslib.LTS.MTr.singleton_iff .. |>.mp lastRun) clean

theorem guarded_iff_filtered :
    GuardedRun profile start xs finish ↔ FilteredRun profile start xs finish := by
  rw [guarded_iff]
  cases h : hasRace profile xs <;> simp [RaceFree, FilteredRun, ClassifiedRun, classify, h]

theorem raceUB_has_raw_run (ub : RaceUB profile start xs) :
    ∃ finish, ClassifiedRun profile start xs finish .racy := by
  obtain ⟨prior, mid, e, finish, rfl, guard, step, race⟩ := ub
  exact ⟨finish, Cslib.LTS.MTr.stepR sc (guarded_iff.mp guard).1 step, by simp [classify, race]⟩

theorem racy_run_has_ub_prefix (run : sc.MTr start xs finish) (race : hasRace profile xs = true) :
    ∃ prior tail, xs = prior ++ tail ∧ RaceUB profile start prior := by
  induction xs using List.reverseRecOn generalizing finish with
  | nil => simp [hasRace] at race
  | append_singleton xs e ih =>
    obtain ⟨mid, prefixRun, lastRun⟩ := run.split
    cases h : hasRace profile xs with
    | false =>
      exact ⟨xs ++ [e], [], by simp, xs, mid, e, finish, rfl,
        guarded_iff.mpr ⟨prefixRun, h⟩, (Cslib.LTS.MTr.singleton_iff ..).mp lastRun, race⟩
    | true =>
      obtain ⟨prior, tail, eq, ub⟩ := ih prefixRun h
      exact ⟨prior, tail ++ [e], by rw [eq, List.append_assoc], ub⟩

theorem raceSafe_iff :
    RaceSafe profile start ↔ ∀ xs finish, sc.MTr start xs finish → RaceFree profile xs := by
  constructor
  · intro safe trace finish run
    apply Bool.eq_false_iff.mpr
    intro race
    obtain ⟨prior, _, _, ub⟩ := racy_run_has_ub_prefix run race
    exact safe prior ub
  · intro safe trace ub
    obtain ⟨finish, run, racy⟩ := raceUB_has_raw_run ub
    simp [classify, safe trace finish run] at racy

end Silmaril.Proofs.Semantics.TrackA.Concurrency
