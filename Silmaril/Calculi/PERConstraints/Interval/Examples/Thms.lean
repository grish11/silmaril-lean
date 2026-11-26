module

public import Silmaril.Calculi.PERConstraints.Interval.Examples.Defs
import Silmaril.Proofs.Calculi.PERConstraints.Interval.Examples

@[expose] public section
namespace Silmaril.Calculi.PERConstraints.IntervalExamples

open Silmaril.Formats Term

theorem either_pair_two_minimal :
    Minimal (· ∈ (full Term).completions (fun model => eitherPair.Holds model)) (pairOnly first middle) ∧
    Minimal (· ∈ (full Term).completions (fun model => eitherPair.Holds model)) (pairOnly middle last) ∧
    pairOnly first middle ≠ pairOnly middle last :=
  Proofs.either_pair_two_minimal

/-- The positive sentence `first = middle ∨ middle = last` has no least model. -/
theorem either_pair_no_least :
    ¬ ∃ model, IsLeast ((full Term).completions (fun candidate => eitherPair.Holds candidate)) model :=
  Proofs.either_pair_no_least

theorem separate_ends_two_maximal :
    Maximal (· ∈ (full Term).completions (fun model => separateEnds.Holds model)) joinFirstMiddle ∧
    Maximal (· ∈ (full Term).completions (fun model => separateEnds.Holds model)) joinMiddleLast ∧
    joinFirstMiddle ≠ joinMiddleLast :=
  Proofs.separate_ends_two_maximal

/-- An upper bound of both exhibited models relates the endpoints by transitivity. -/
theorem separate_ends_no_greatest :
    ¬ ∃ model, IsGreatest ((full Term).completions (fun candidate => separateEnds.Holds candidate)) model :=
  Proofs.separate_ends_no_greatest

/-- Both endpoints reject the same CNF, but an interior PER satisfies it. -/
theorem distinct_interior_only :
    ¬ separateBools.Holds (full Bool).lower ∧ ¬ separateBools.Holds (full Bool).upper ∧
    (full Bool).Possible (fun _ => True) (fun model => separateBools.Holds model) :=
  Proofs.distinct_interior_only

theorem collapse_possible_strict :
    ((full Unit).pull collapse).Possible (fun _ => True) (fun model => separateBools.Holds model) ∧
    ¬ (full Unit).Possible (fun _ => True) (fun model => (separateBools.map collapse).Holds model) :=
  Proofs.collapse_possible_strict

/-- Even a least model of a translated EQ can reduce to a non-least model. -/
theorem collapse_reduct_not_least :
    IsLeast ((full Unit).completions (fun model => (requireFalse.map collapse).Holds model)) (PER.equality Unit) ∧
    ¬ IsLeast (((full Unit).pull collapse).completions (fun model => requireFalse.Holds model))
      ((PER.equality Unit).pull collapse) :=
  Proofs.collapse_reduct_not_least

theorem conflict_fiber_empty :
    (full Bool).completions (fun model => (Dictionary.toCNF Examples.conflict).Holds model) = ∅ :=
  Proofs.conflict_fiber_empty

end Silmaril.Calculi.PERConstraints.IntervalExamples
