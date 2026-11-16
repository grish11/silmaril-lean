module

public import Silmaril.Logic.Consequence.Institution.Thms

/-!
# Local and global consequence differ: examples

One model with two points (valuations) `true` and `false`, and two formulas `true` and `false`
standing for `x` and `¬x`: the formula `c` holds at the point `p` iff `p = c`.

* `⊢ x, ¬x` holds **locally** (every valuation satisfies one of them) and fails **globally**
  (neither is valid in the model). So a model-wise Gentzen succedent is not the point-wise
  (classical, disjunctive) one, and neither multiple-conclusion system is below the other.
* `x ⊢ ¬x` holds globally (no model validates `x`) and fails locally: global single-conclusion
  consequence is not below local consequence. The other direction always holds
  (`entails_localSat_le_validIn`).
-/

@[expose] public section

namespace Silmaril.Consequence.Examples.LocalGlobal

open Silmaril.Consequence

/-- `c` holds at the point `p` iff `p = c`. -/
def sat : (_ : Unit) → Bool → Bool → Prop := fun _ p c => p = c

example : Gentzen.Valid (localSat sat) [] [true, false] := by
  rintro ⟨_, p⟩ -
  cases p <;> simp [localSat, sat]

example : ¬ Gentzen.Valid (validIn sat) [] [true, false] := by
  intro h
  obtain ⟨d, -, hd⟩ := h () (by simp [Refutation.SatAll])
  cases d
  · exact absurd (hd true) (by simp [sat])
  · exact absurd (hd false) (by simp [sat])

example : Refutation.Entails (validIn sat) [true] false := by
  intro m hm
  exact absurd (hm true (by simp) false) (by simp [sat])

example : ¬ Refutation.Entails (localSat sat) [true] false := by
  intro h
  exact absurd (h ⟨(), true⟩ (by simp [Refutation.SatAll, localSat, sat])) (by simp [localSat, sat])

end Silmaril.Consequence.Examples.LocalGlobal
