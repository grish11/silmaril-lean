module

public import Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Institution

set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Examples
open Silmaril.Logic.Smt

/-- A symbolic refutation, for any supported pattern and arbitrary valuation. -/
theorem contradiction {s : ValueSort} (p : Pattern s) (v : Valuation) :
    (Pattern.conj p (.neg p)).denote v = ∅ := by
  ext x
  simp [Pattern.denote]

theorem compiled_contradiction {s : ValueSort} (p : Pattern s) (point : Point s) :
    ¬ Uflia.Quantified.Formula.Holds (Pattern.conj p (.neg p)).characteristic
      (target point.1) (fun _ => point.2) := by
  rw [characteristic_correct, contradiction]
  simp

/-- Set-valued arguments are essential: equality of any two integers can
produce either Boolean result. This is not equality of the two input sets. -/
theorem equality_top (v : Valuation) :
    (Pattern.intEq (.top .integer) (.top .integer)).denote v = Set.univ := by
  ext b
  simp only [Pattern.denote, Set.mem_ofPred_eq, Set.mem_univ, true_and, iff_true]
  cases b with
  | false => exact ⟨(0 : Int), (1 : Int), by
      change (false : Bool) = Operational.Conditional.intEqual 0 1
      rfl⟩
  | true => exact ⟨(0 : Int), (0 : Int), by
      change (true : Bool) = Operational.Conditional.intEqual 0 0
      rfl⟩

theorem equality_empty (v : Valuation) (p : Pattern .integer) :
    (Pattern.intEq p (.bottom .integer)).denote v = ∅ := by
  ext b
  simp [Pattern.denote]

/-- Repeating one set-valued variable does not force integer equality to true:
the two argument occurrences may select different members of the same set. -/
theorem repeated_variable_false (v : Valuation) (name : String) (x y : Int)
    (hx : x ∈ v .integer name) (hy : y ∈ v .integer name) (different : x ≠ y) :
    false ∈ (Pattern.intEq (.variable .integer name) (.variable .integer name)).denote v := by
  refine ⟨x, hx, y, hy, ?_⟩
  simp [Operational.Conditional.intEqual, different]

/-- Hook value-negation of the universal Boolean set is universal; set
complement of that same set is empty. The compiler must preserve this gap. -/
theorem value_not_top (v : Valuation) :
    (Pattern.boolNot (.top .boolean)).denote v = Set.univ := by
  ext b
  simp only [Pattern.denote, Set.mem_ofPred_eq, Set.mem_univ, true_and, iff_true]
  exact ⟨!b, by cases b <;> rfl⟩

theorem complement_top (v : Valuation) :
    (Pattern.neg (.top .boolean)).denote v = ∅ := by
  ext b
  simp [Pattern.denote]

end Silmaril.Logic.Kore.GeneralFixedPoint.Builtins.Smt.Examples
