module

public import Silmaril.Semantics.Accept.Success.Thms

/-! # Successful-value projections: worked examples and regression tests

A nondeterministic `Option`-valued decoder (`halfOrNone`), an `Except`-valued checker and a
WIT-style `result` (`ℕ ⊕ String`). Every `example` is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.SuccessExamples

open Silmaril.Accept
open scoped SetRel

/-- Halve even numbers; on any input the program may also give up with `none`. -/
def halfOrNone : ℕ -|> Option ℕ :=
  {p | p.2 = none ∨ (p.1 % 2 = 0 ∧ p.2 = some (p.1 / 2))}

example : ((4 : ℕ), (2 : ℕ)) ∈ someVals halfOrNone := by simp [halfOrNone]
example : ((5 : ℕ), (2 : ℕ)) ∉ someVals halfOrNone := by simp [halfOrNone]

/-- `5` only ever answers `none`, so it has no successful value. -/
example : (5 : ℕ) ∉ (someVals halfOrNone).dom :=
  not_mem_dom_someVals fun c hc => by simp_all [halfOrNone]

/-- Some successful value of `4` is small. -/
example : (4 : ℕ) ∈ pullSome (someVals halfOrNone) {n | n < 3} := ⟨2, by simp, by simp [halfOrNone]⟩

/-- Every successful value of `5` is small, vacuously. -/
example : (5 : ℕ) ∈ pullAll (someVals halfOrNone) {n | n < 3} := fun b hb => by
  simp [halfOrNone] at hb

/-- A checker that fails with a message on odd numbers. -/
def evenCheck (n : ℕ) : Except String ℕ := if n % 2 = 0 then .ok n else .error "odd"

example : ((6 : ℕ), (6 : ℕ)) ∈ okVals (ofTotal evenCheck) := by simp [evenCheck]
example : ((7 : ℕ), "odd") ∈ errVals (ofTotal evenCheck) := by simp [evenCheck]
example : (7 : ℕ) ∉ (okVals (ofTotal evenCheck)).dom :=
  not_mem_dom_okVals fun c hc => ⟨"odd", by simp_all [evenCheck]⟩

/-- `okVals` of a total map is a partial function. -/
example : okVals (ofTotal evenCheck) = ofPartial (exceptOk ∘ evenCheck) := succ_ofTotal

/-- A WIT `result<u32, string>`-style answer: `inl` is `ok`. -/
def wit (n : ℕ) : ℕ ⊕ String := if n < 10 then .inl (n + 1) else .inr "too big"

example : ((3 : ℕ), (4 : ℕ)) ∈ inlVals (ofTotal wit) := by simp [wit]
example : ((30 : ℕ), "too big") ∈ inrVals (ofTotal wit) := by simp [wit]
example : ((30 : ℕ), (31 : ℕ)) ∉ inlVals (ofTotal wit) := by simp [wit]

/-- Projecting twice: the `some` values of the `inl` values. -/
example : succ optionOk (inlVals (ofTotal fun n : ℕ => (.inl (some n) : Option ℕ ⊕ Unit))) =
    succ (partialComp sumOk optionOk) (ofTotal fun n : ℕ => (.inl (some n) : Option ℕ ⊕ Unit)) :=
  succ_comp

/-- A partial function stays single-valued after projection. -/
example : ∀ a b b', (a, b) ∈ okVals (ofTotal evenCheck) → (a, b') ∈ okVals (ofTotal evenCheck) →
    b = b' :=
  succ_single fun _ _ _ h h' => h.symm.trans h'

end Silmaril.Accept.SuccessExamples
