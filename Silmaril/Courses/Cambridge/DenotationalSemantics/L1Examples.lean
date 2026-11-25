module

import Silmaril.Courses.Cambridge.L1.DenotationalInstitution

/-! Checked store-dependent returns, a skipped read, and a reached stuck term. -/

open CategoryTheory Silmaril.Logic.Fragments
open Silmaril.Courses.Cambridge.L1
open Silmaril.Courses.Cambridge.L1.Denotational
open Silmaril.Courses.Cambridge.L1.DenotationalInstitution

-- The else branch would read a missing location in both stores below.
private def program : Expr :=
  .cond (.binary (.deref "x") .ge (.int 0))
    (.binary (.deref "x") .add (.int 2)) (.deref "missing")

private theorem readOnly : ReadOnly program :=
  .cond (.binary (.deref _) (.int _)) (.binary (.deref _) (.int _)) (.deref _)

private def input (n : Int) : Store := Store.empty.insert "x" n

example : denote program (input 5) = some (.int 7) ∧
    denote program (input 9) = some (.int 11) :=
  ⟨by simp [program, input, denote], by simp [program, input, denote]⟩

private theorem satisfies : (atomicInstitution.obj signature).Sat (Discrete.mk model)
    (⟨⟨program, input 5⟩, readOnly⟩, ⟨.int 7, input 5⟩) := by
  change denote program (input 5) = some (.int 7) ∧ input 5 = input 5
  exact ⟨by simp [program, input, denote], rfl⟩

example : OperationalInstitution.semantics.May ⟨program, input 5⟩
    (.returned ⟨.int 7, input 5⟩) :=
  (sat_iff _ _).mp satisfies

example : ¬ (atomicInstitution.obj signature).Sat (Discrete.mk model)
    (⟨⟨program, input 5⟩, readOnly⟩, ⟨.int 7, input 9⟩) := by
  intro claim
  change denote program (input 5) = some (.int 7) ∧ input 9 = input 5 at claim
  have lookup := congrArg (fun s : Store => s.lookup "x") claim.2
  simp [input] at lookup

example : ∃ t, Steps ⟨program, input (-1)⟩ t ∧ Stuck t :=
  (denote_eq_none_iff readOnly).1 (by
    simp [program, input, denote, Store.lookup_insert_other])

example : denote (.binary (.bool true) .add (.int 2)) Store.empty = none := rfl
