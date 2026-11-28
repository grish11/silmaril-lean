module

public import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.DependentRequestTree.Native.OpenOperands.Step.Product.Search.Replay.Schedule.Defs

public section

namespace Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands

universe u

variable {Φ : Type u} [HasTy Φ Syntax.Ty] {states : Nat}

private theorem sameAnswer_iff {A : Syntax.Ty} (p q : Syntax.Reply A states) :
    InterpreterScript.sameAnswer p q = true ↔ p = q := by
  cases p <;> cases q <;> simp [InterpreterScript.sameAnswer, Subtype.ext_iff]

private theorem transport_symm {p q : InterpreterScript.Query Φ states} (same : p = q)
    {a : Syntax.Reply (instrTrg p.op) states} {b : Syntax.Reply (instrTrg q.op) states}
    (eq : (same.symm ▸ b : Syntax.Reply (instrTrg p.op) states) = a) :
    (same ▸ a : Syntax.Reply (instrTrg q.op) states) = b := by
  cases same
  exact eq.symm

theorem consistent_subset {rows more : List (InterpreterScript.Row Φ states)} (covers : rows ⊆ more)
    (ok : InterpreterScript.Consistent more) : InterpreterScript.Consistent rows :=
  fun a ha b hb same => ok a (covers ha) b (covers hb) same

variable [DecidableEq Φ]

private theorem compatible_iff (rows : List (InterpreterScript.Row Φ states)) (row : InterpreterScript.Row Φ states) :
    InterpreterScript.canAppend rows row = true ↔
      ∀ previous ∈ rows, ∀ same : previous.1 = row.1,
        (same ▸ previous.2 : Syntax.Reply (instrTrg row.1.op) states) = row.2 := by
  rw [InterpreterScript.canAppend, List.all_eq_true]
  constructor
  · intro all old listed same
    have allowed := all old listed
    simp only [InterpreterScript.Row.lookup, dite_eq_left same] at allowed
    exact (sameAnswer_iff _ _).mp allowed
  · intro compatible old listed
    by_cases same : old.1 = row.1
    · simp only [InterpreterScript.Row.lookup, dite_eq_left same]
      exact (sameAnswer_iff _ _).mpr (compatible old listed same)
    · simp [InterpreterScript.Row.lookup, same]

theorem can_append_iff {rows : List (InterpreterScript.Row Φ states)} {row : InterpreterScript.Row Φ states}
    (ok : InterpreterScript.Consistent rows) :
    InterpreterScript.canAppend rows row = true ↔ InterpreterScript.Consistent (rows ++ [row]) := by
  rw [compatible_iff]
  constructor
  · intro compatible a ha b hb same
    rcases List.mem_append.mp ha with oldA | newA <;> rcases List.mem_append.mp hb with oldB | newB
    · exact ok a oldA b oldB same
    · obtain rfl := List.mem_singleton.mp newB
      exact compatible a oldA same
    · obtain rfl := List.mem_singleton.mp newA
      exact transport_symm same (compatible b oldB same.symm)
    · obtain rfl := List.mem_singleton.mp newA
      obtain rfl := List.mem_singleton.mp newB
      rfl
  · intro all previous listed same
    exact all previous (List.mem_append_left _ listed) row (List.mem_append_right _ (List.mem_singleton_self _)) same

theorem can_append_all_iff {rows : List (InterpreterScript.Row Φ states)} (ok : InterpreterScript.Consistent rows)
    (more : List (InterpreterScript.Row Φ states)) :
    InterpreterScript.canAppendAll rows more = true ↔ InterpreterScript.Consistent (rows ++ more) := by
  induction more generalizing rows with
  | nil => simp [InterpreterScript.canAppendAll, ok]
  | cons row rest ih =>
    rw [InterpreterScript.canAppendAll, Bool.and_eq_true_iff]
    constructor
    · rintro ⟨first, tail⟩
      simpa using (ih ((can_append_iff ok).mp first)).mp tail
    · intro all
      have first : InterpreterScript.Consistent (rows ++ [row]) :=
        consistent_subset (fun _ mem => List.mem_append.mpr ((List.mem_append.mp mem).imp id
          fun one => (List.mem_singleton.mp one) ▸ List.mem_cons_self)) all
      exact ⟨(can_append_iff ok).mpr first, (ih first).mpr (by simpa using all)⟩

end Silmaril.Proofs.Isotope.LambdaSSA.UB.Overlay.Shape.DependentRequestTree.NativeExtraction.OpenOperands.ScheduleSearch
