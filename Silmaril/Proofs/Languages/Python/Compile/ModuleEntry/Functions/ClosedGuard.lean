module

public import Silmaril.Languages.Python.Compile.ModuleEntry.Functions.Defs
public import Silmaril.Numeric.Ieee754.CoreFloat

public section
namespace Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard

open Silmaril.Languages.Python
open Compile.ModuleEntry.Functions
open Compile.ModuleEntry.Functions.ClosedGuard
open Silmaril.Numeric.Ieee754 (F64)

theorem select_iff (operator : Source.BooleanOperator) (first : Value)
    (rest : List Value) (result : Value) :
    select operator first rest = result ↔ Selects operator first rest result := by
  induction rest generalizing first with
  | nil =>
    constructor
    · intro found
      change first = result at found
      subst result
      exact .last first
    · intro selected
      cases selected
      rfl
  | cons next rest ih =>
    cases continued : continues operator first with
    | false =>
      simp only [select, continued, Bool.false_eq_true, ite_false]
      constructor
      · intro found
        subst result
        exact .stop continued
      · intro selected
        cases selected with
        | stop => rfl
        | next progressed _ => simp [continued] at progressed
    | true =>
      simp only [select, continued, ite_true, ih]
      constructor
      · exact .next continued
      · intro selected
        cases selected with
        | stop stopped => simp [continued] at stopped
        | next _ following => exact following

theorem checkedLinks_iff (left : Value) (links : List (Source.Comparison × Value))
    (results : List Bool) :
    checkedLinks left links = some results ↔ ChecksLinks left links results := by
  induction links generalizing left results with
  | nil =>
    constructor
    · intro found
      change some [] = some results at found
      cases found
      exact .done left
    · intro checked
      cases checked
      rfl
  | cons link rest ih =>
    obtain ⟨operator, right⟩ := link
    constructor
    · intro found
      cases resultEq : compare? operator left right with
      | none => simp [checkedLinks, resultEq] at found
      | some result =>
        cases tailEq : checkedLinks right rest with
        | none => simp [checkedLinks, resultEq, tailEq] at found
        | some tail =>
          have equal : result :: tail = results := by simpa [checkedLinks, resultEq, tailEq] using found
          cases equal
          exact .next resultEq ((ih right tail).mp tailEq)
    · intro checked
      cases checked with
      | next first following =>
        simp [checkedLinks, first, (ih _ _).mpr following]

theorem add_float_result {left right result : F64.Finite}
    (checked : binary? .add (.float left) (.float right) = some (.float result)) :
    result.val = F64.ofFloat (left.val.toFloat + right.val.toFloat) := by
  simp only [binary?, F64.Finite.add?, F64.Finite.map₂?, F64.Finite.ofRaw?] at checked
  split at checked
  · cases checked
    exact F64.add_eq_float left.val right.val
  · cases checked

theorem testFloat_runtime (operator : Compile.ModuleEntry.ScalarComparison) (left right : F64) :
    testFloat operator left right = (match operator with
      | .eq => left.toFloat == right.toFloat
      | .ne => !(left.toFloat == right.toFloat)
      | .lt => left.toFloat.lt right.toFloat
      | .le => left.toFloat.le right.toFloat
      | .gt => right.toFloat.lt left.toFloat
      | .ge => right.toFloat.le left.toFloat) := by
  cases operator <;>
    simp [testFloat, F64.equal_eq_float, F64.lessThan_eq_float, F64.lessEqual_eq_float]

theorem selected_pass {condition yes no value} (checked : Omitted (.if_ condition yes no) value) :
    ∀ statement ∈ (if value.truth then yes else no), statement = .pass := by
  cases checked with
  | conditional _ _ selected _ _ =>
    intro statement present
    have pass := List.all_eq_true.mp selected statement present
    cases statement <;> simp_all [isPass]

theorem lowerPlan_omitted {tree : Source.ScopeTree} {index : Nat}
    {condition : Source.Expr} {yes no rest : List Source.Stmt}
    {witness} (checked : omitted? (.if_ condition yes no) = some witness) :
    (lowerPlan tree index (.if_ condition yes no :: rest)).toOption.map Subtype.val =
      (lowerPlan tree index rest).toOption.map Subtype.val := by
  rw [lowerPlan]
  · simp only [checked]
    cases lowerPlan tree index rest <;> rfl
  all_goals simp

end Silmaril.Proofs.Languages.Python.Compile.ModuleEntry.Functions.ClosedGuard
