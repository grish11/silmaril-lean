module

public import Silmaril.Languages.Starlark.Lists.Defs
import Silmaril.Languages.Starlark.Binary64.Thms

public section

namespace Silmaril.Proofs.Languages.Starlark.Lists

open Silmaril.Languages.Starlark.Lists
open Silmaril.Languages.Starlark (applyBinary comparisonResult)
open Silmaril.Languages.Starlark.Binary64 (Number compareNumbers orders_iff_compareNumbers)

private theorem ofInt_eq_iff_eq (left right : Int) : Number.ofInt left = Number.ofInt right ↔ left = right := by
  have scale : (2 ^ 1074 : Int) ≠ 0 := Int.pow_ne_zero (by decide)
  rw [Number.ofInt, Number.ofInt, Number.finite.injEq, Int.mul_eq_mul_right_iff scale]

private theorem scalarCode_eq_iff_eq (left right : Silmaril.Languages.Starlark.Value) :
    ScalarKey.ofValue left = ScalarKey.ofValue right ↔ applyBinary .eq left right = .ok (.bool true) := by
  have numeric (a b : Number) : compareNumbers a b = .eq ↔ a = b :=
    (orders_iff_compareNumbers a b .eq).symm
  cases left <;> cases right <;>
    simp [ScalarKey.ofValue, ScalarKey.int, applyBinary, comparisonResult,
      Silmaril.Languages.Starlark.Value.orderedCompare, Silmaril.Languages.Starlark.Value.isNone,
      numeric, ofInt_eq_iff_eq]

theorem scalar_key_eq_iff_eq (s t : State) (left right : Silmaril.Languages.Starlark.Value) :
    s.keyOf (.scalar left) = t.keyOf (.scalar right) ↔ applyBinary .eq left right = .ok (.bool true) := by
  simpa [State.keyOf] using scalarCode_eq_iff_eq left right

theorem putEntry_keys (entry : Entry) (entries : List Entry) :
    (putEntry entry entries).map Entry.key =
      if (findEntry entry.keyCode entries).isSome then entries.map Entry.key
      else entries.map Entry.key ++ [entry.key] := by
  induction entries with
  | nil => rfl
  | cons old rest ih =>
    by_cases found : (old.keyCode == entry.keyCode) = true
    · simp [putEntry, findEntry, found]
    · simp [putEntry, findEntry, found] at *
      rw [ih]
      split <;> rfl

end Silmaril.Proofs.Languages.Starlark.Lists
