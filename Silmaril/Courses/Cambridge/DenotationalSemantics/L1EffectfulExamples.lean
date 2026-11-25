module

import Silmaril.Courses.Cambridge.L1.EffectfulDenotational.Institution

/-! Checked Elgot iteration over the original L1 stores and reduction rules. -/

open CategoryTheory Silmaril Silmaril.Logic.Fragments
open Silmaril.Courses.Cambridge.L1
open Silmaril.Courses.Cambridge.L1.EffectfulDenotational

private theorem loop_continue {test body : Expr} {s t u : Store}
    (guard : run (denote test) s = Part.some (.ok (.bool true), t))
    (command : run (denote body) t = Part.some (.ok .skip, u)) :
    run (denote (.loop test body)) s = run (denote (.loop test body)) u := by
  conv_lhs => rw [denote_loop_unfold, denote, run_bind, guard, Part.bind_some]
  change run (denote (.seq body (.loop test body))) t = _
  rw [denote, run_bind, command, Part.bind_some]
  rfl

private theorem loop_exit {test body : Expr} {s t : Store}
    (guard : run (denote test) s = Part.some (.ok (.bool false), t)) :
    run (denote (.loop test body)) s = Part.some (.ok .skip, t) := by
  rw [denote_loop_unfold, denote, run_bind, guard, Part.bind_some]
  rfl

private def sumTest : Expr := .binary (.deref "x") .ge (.int 1)
private def sumBody : Expr :=
  .seq (.assign "acc" (.binary (.deref "acc") .add (.deref "x")))
    (.assign "x" (.binary (.deref "x") .add (.int (-1))))
private def program : Expr := .seq (.loop sumTest sumBody) (.deref "acc")

private def initial : Store := (Store.empty.insert "x" 3).insert "acc" 0
private def first : Store := (initial.insert "acc" 3).insert "x" 2
private def second : Store := (first.insert "acc" 5).insert "x" 1
private def final : Store := (second.insert "acc" 6).insert "x" 0

private theorem run_sumTest {s : Store} (x : Int) (counter : s.lookup "x" = some x) :
    run (denote sumTest) s = Part.some (.ok (.bool (x ≥ 1)), s) := by
  simp [sumTest, denote, run_bind, binary, Part.bind_some, counter]

private theorem run_sumBody {s : Store} (x acc : Int)
    (counter : s.lookup "x" = some x) (total : s.lookup "acc" = some acc) :
    run (denote sumBody) s =
      Part.some (.ok .skip, (s.insert "acc" (acc + x)).insert "x" (x + (-1))) := by
  have accPresent : "acc" ∈ s := Finmap.mem_of_lookup_eq_some total
  have xAfter : (s.insert "acc" (acc + x)).lookup "x" = some x := by
    rw [Finmap.lookup_insert_of_ne s (by decide : "x" ≠ "acc")]
    exact counter
  have xPresent : "x" ∈ s.insert "acc" (acc + x) := Finmap.mem_of_lookup_eq_some xAfter
  simp [sumBody, denote, run_bind, binary, assign, afterSkip, Part.bind_some, counter, total,
    Store.update_eq_some _ _ _ accPresent, Store.update_eq_some _ _ _ xPresent]

private theorem loop_result :
    run (denote (.loop sumTest sumBody)) initial = Part.some (.ok .skip, final) := by
  calc
    _ = run (denote (.loop sumTest sumBody)) first := loop_continue
      (run_sumTest 3 (by simp [initial, Store.lookup_insert_other]))
      (run_sumBody 3 0 (by simp [initial, Store.lookup_insert_other]) (by simp [initial]))
    _ = run (denote (.loop sumTest sumBody)) second := loop_continue
      (run_sumTest 2 (by simp [first]))
      (run_sumBody 2 3 (by simp [first]) (by simp [first, Store.lookup_insert_other]))
    _ = run (denote (.loop sumTest sumBody)) final := loop_continue
      (run_sumTest 1 (by simp [second]))
      (run_sumBody 1 5 (by simp [second]) (by simp [second, Store.lookup_insert_other]))
    _ = _ := loop_exit (run_sumTest 0 (by simp [final]))

private theorem sum_result : run (denote program) initial = Part.some (.ok (.int 6), final) := by
  rw [program, denote, run_bind, loop_result, Part.bind_some]
  simp [afterSkip, denote, final, Store.lookup_insert_other]

example : (atomicInstitution.obj Institution.signature).Sat (Discrete.mk Institution.model)
    (⟨program, initial⟩, ⟨.int 6, final⟩) := by
  change (.ok (.int 6), final) ∈ run (denote program) initial
  rw [sum_result]
  exact Part.mem_some _

example : OperationalInstitution.semantics.May ⟨program, initial⟩ (.returned ⟨.int 6, final⟩) :=
  (Institution.sat_iff _ _).1 (show (.ok (.int 6), final) ∈ run (denote program) initial by
    rw [sum_result]
    exact Part.mem_some _)

-- An assignment before a failing write remains visible at the stuck state.
private def failing : Expr :=
  .seq (.assign "x" (.int 2)) (.assign "missing" (.int 1))

private theorem failing_result : (.error (), initial.insert "x" 2) ∈ run (denote failing) initial := by
  simp [failing, initial, denote, run_bind, assign, afterSkip, Part.bind_some, Store.update,
    Store.empty, Finmap.notMem_empty]

example : ∃ e, Steps ⟨failing, initial⟩ ⟨e, initial.insert "x" 2⟩ ∧
    Stuck ⟨e, initial.insert "x" 2⟩ :=
  error_iff.1 failing_result

private def spin : Expr := .loop (.bool true) .skip

open Silmaril.Elgot in
private theorem spin_result (s : Store) : run (denote spin) s = Part.none := by
  change iter (Elgot.StateT.body (Elgot.ExceptT.body
    (whileBody (denote (.bool true)) (denote .skip)))) ((), s) = Part.none
  have bodyEq : Elgot.StateT.body (Elgot.ExceptT.body
      (whileBody (denote (.bool true)) (denote .skip))) =
      fun p => Part.some (.inr p) := by
    funext p
    rcases p with ⟨⟨⟩, store⟩
    simp [Elgot.StateT.body, Elgot.ExceptT.body, whileBody, denote, branch, afterSkip,
      Elgot.ExceptT.distribute, Elgot.StateT.distribute]
  simp [bodyEq]

example (s : Store) : InfiniteTrace Step ⟨spin, s⟩ :=
  diverges_iff.2 (by simp [spin_result])

-- L1 evaluates the right operand after any left value, even an ill-shaped one.
example (s : Store) : run (denote (.binary (.bool true) .add spin)) s = Part.none := by
  rw [denote, denote, pure_bind, run_bind, spin_result]
  simp
