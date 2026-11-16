module

public import Silmaril.Semantics.Accept.Func.Thms

/-! # The functional shape of relations: counterexamples and regression tests

The four notions are independent: a total relation need not be single-valued, a
single-valued one need not be total, an injective one need not be surjective, and a
surjective one need not be total. Every `example` is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.FuncExamples

open Silmaril.Accept
open scoped SetRel

/-- Every Boolean relates to every Boolean. -/
def anyBool : Bool -|> Bool := Set.univ

/-- A partial decoder: halves even numbers, fails on odd ones. -/
def half (n : ℕ) : Option ℕ := if n % 2 = 0 then some (n / 2) else none

/-- Total but not single-valued. -/
example : Total anyBool := fun _ => ⟨true, trivial⟩
example : ¬ SingleValued anyBool := fun h => Bool.false_ne_true (h (a := true) trivial trivial)

/-- Single-valued but not total: `1` has no half. -/
example : SingleValued (ofPartial half) := singleValued_ofPartial half
example : ¬ Total (ofPartial half) := fun h =>
  let ⟨_, hb⟩ := h 1; by simp [half] at hb

/-- Surjective but not total: every `n` is the half of `2 * n`, yet `1` has no output. -/
example : Surjective (ofPartial half) := fun n => ⟨2 * n, by simp [half]⟩
example : ¬ (Surjective (ofPartial half) → Total (ofPartial half)) := fun h =>
  let ⟨_, hb⟩ := h (fun n => ⟨2 * n, by simp [half]⟩) 1; by simp [half] at hb

/-- Injective but not surjective: the successor misses `0`. -/
example : Injective (ofTotal Nat.succ) := injective_ofTotal_iff.2 Nat.succ_injective
example : ¬ Surjective (ofTotal Nat.succ) := fun h =>
  let ⟨_, hb⟩ := h 0; Nat.succ_ne_zero _ hb

/-- Extraction recovers the partial function, and the total map. -/
example : toPartial (ofPartial half) 4 = some 2 := by simp [half]
example : toFun (total_ofTotal Nat.succ) 3 = 4 := by simp

/-- Along a functional relation the two pullbacks agree. -/
example (L : Set ℕ) : pullSome (ofTotal Nat.succ) L = pullAll (ofTotal Nat.succ) L :=
  (functional_ofTotal _).pullSome_eq_pullAll

/-- Along a single-valued relation, existential acceptance implies universal. -/
example (L : Set ℕ) : pullSome (ofPartial half) L ⊆ pullAll (ofPartial half) L :=
  (singleValued_ofPartial half).pullSome_subset_pullAll

end Silmaril.Accept.FuncExamples
