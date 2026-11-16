module

public import Silmaril.Semantics.Accept.MonoidRegex.Thms

/-! # Regular expressions over a monoid: worked examples

* **Natural numbers under addition** (`Multiplicative ℕ`): the star of the atom `2` is the even
  numbers, and `2* · 3` (product = addition) is the odd numbers that are at least 3. These are
  languages of numbers, not of digit strings: no encoding is involved.
* **The list case**: a byte regular expression of `Silmaril.Accept.Regex`, evaluated over the
  free monoid, has the same members as the existing list semantics (`mem_eval_ofRegex`).

Every `example` is checked when the library builds.
-/

@[expose] public section

namespace Silmaril.Accept.MonoidRegexExamples

open Silmaril.Accept.MonoidRegex Silmaril.Accept.MonoidRegex.Expr

/-! ## `ℕ` under addition -/

/-- The atom `2` of the additive monoid `ℕ`, written multiplicatively. -/
def two : Multiplicative ℕ := Multiplicative.ofAdd 2

/-- `2*`: the sums of finitely many `2`s. -/
def evens : Expr Empty (Multiplicative ℕ) := star (atom two)

theorem prod_replicate_two (k : ℕ) :
    ((List.replicate k two).prod : Multiplicative ℕ) = Multiplicative.ofAdd (2 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.prod_cons, ih]
    change Multiplicative.ofAdd (2 + 2 * k) = Multiplicative.ofAdd (2 * (k + 1))
    congr 1; omega

/-- `2*` denotes exactly the even numbers. -/
theorem mem_evens (n : ℕ) :
    Multiplicative.ofAdd n ∈ eval Empty.elim evens ↔ n % 2 = 0 := by
  change (∃ l : List (Multiplicative ℕ), (∀ y ∈ l, y = two) ∧ l.prod = Multiplicative.ofAdd n) ↔ _
  constructor
  · rintro ⟨l, hl, hprod⟩
    have hrep : l = List.replicate l.length two := List.eq_replicate_iff.mpr ⟨rfl, hl⟩
    rw [hrep, prod_replicate_two] at hprod
    have : 2 * l.length = n := congrArg Multiplicative.toAdd hprod
    omega
  · intro h
    refine ⟨List.replicate (n / 2) two, fun y hy => List.eq_of_mem_replicate hy, ?_⟩
    rw [prod_replicate_two]
    congr 1
    omega

example : Multiplicative.ofAdd 6 ∈ eval Empty.elim evens := (mem_evens 6).mpr rfl

example : Multiplicative.ofAdd 7 ∉ eval Empty.elim evens := fun h =>
  absurd ((mem_evens 7).mp h) (by decide)

/-- `2* · 3`: products are sums, so these are the odd numbers from `3` on. -/
def oddsFromThree : Expr Empty (Multiplicative ℕ) := comp evens (atom (Multiplicative.ofAdd 3))

example : Multiplicative.ofAdd 7 ∈ eval Empty.elim oddsFromThree :=
  ⟨Multiplicative.ofAdd 4, (mem_evens 4).mpr rfl, Multiplicative.ofAdd 3, rfl, rfl⟩

/-! ## The list case -/

/-- `a b*` over bytes, as a `Silmaril.Accept.Regex` expression. -/
def abStar : Silmaril.Accept.Regex.Expr Empty UInt8 :=
  .comp (.char 0x61) (.star (.char 0x62))

/-- Over the free monoid, the same word is a member (the bridge `mem_eval_ofRegex`). -/
example (w : List UInt8) :
    FreeMonoid.ofList w ∈ eval (fun i => FreeMonoid.toList ⁻¹' Empty.elim i) (ofRegex abStar) ↔
      w ∈ Silmaril.Accept.Regex.Expr.eval Empty.elim abStar :=
  mem_eval_ofRegex Empty.elim abStar w

end Silmaril.Accept.MonoidRegexExamples
