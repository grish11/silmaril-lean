module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Syntax.Thms
import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Category.Iteration.Finite.Thms

/-! # Generate and compare stateful loop tables from typed overlay syntax -/

open Silmaril
open Silmaril.Isotope
open Silmaril.Isotope.LambdaSSA.UB.Overlay
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration
open Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.Category.FiniteIteration.Syntax

namespace LambdaSSAUBFiniteSyntaxRegression

private abbrev U : Silmaril.Ty Empty := .unit
private abbrev Exit : Silmaril.Ty Empty := .coprod U U
private abbrev Route : Silmaril.Ty Empty := .coprod Exit U
private abbrev State := Fin 6

local instance : HasTy Unit (Silmaril.Ty Empty) := ⟨fun _ => U, fun _ => Route⟩

private def primitive : Primitives Unit 6 := fun _ _ s =>
  match s.val with
  | 0 => .ret ⟨.inl (.inr .unit), .inl (.inr .unit)⟩ 1
  | 1 => .ret ⟨.inr .unit, .inr .unit⟩ 1
  | 2 => .fault 3
  | 3 => .ret ⟨.inl (.inl .unit), .inl (.inl .unit)⟩ 3
  | 4 => .diverge
  | _ => .ret ⟨.inl (.inr .unit), .inl (.inr .unit)⟩ 5

private def body (allowUB : Bool) : Program Unit [U, U] Exit :=
  .call () (.var 0)
    (.case (.var 0) (.ret (.var 0)) (if allowUB then .ub else .ret (.inl .unit)))

private abbrev unitPayload : Payload U := ⟨.unit, .unit⟩

private def unitCode : Fin 1 ≃ Payload U where
  toFun _ := unitPayload
  invFun _ := 0
  left_inv i := (Fin.eq_zero i).symm
  right_inv a := by
    obtain ⟨_, h⟩ := a
    cases h
    rfl

private def codes : Codes U U U 1 1 1 := ⟨fun _ => unitPayload, unitCode, unitCode⟩

private abbrev table (allowUB : Bool) := generate codes primitive (body allowUB)

private noncomputable abbrev observed (allowUB : Bool) (s : State) :=
  (iterateCaptured (model primitive emptyBindings) (body allowUB).region).run 0
    (pairPayload unitPayload unitPayload) s

private theorem changing_repeat : ∃ next, table true 0 0 = .repeat next ∧
    (codes.carrier primitive).invocation next = (unitPayload, (1 : State)) :=
  ⟨1, rfl, rfl⟩

private theorem classify_start (allowUB : Bool) (s : State) :
    observed allowUB s =
      (execute (table allowUB 0) (finProdFinEquiv (0, s))).behaviour (codes.carrier primitive) := by
  have decoded : (codes.carrier primitive).invocation (finProdFinEquiv (0, s)) = (unitPayload, s) := by
    change (let p := finProdFinEquiv.symm (finProdFinEquiv ((0 : Fin 1), s))
            (unitPayload, p.2)) = _
    rw [Equiv.symm_apply_apply]
  have captured : (codes.carrier primitive).capture 0 = unitPayload := rfl
  simpa only [decoded, captured] using
    classify (codes.carrier primitive) _ _ (generate_certified codes primitive (body allowUB))
      0 (finProdFinEquiv (0, s))

private theorem reaches_ub : observed true 0 = ⊤ :=
  (classify_start true 0).trans rfl

private theorem returns_after_repeat : observed false 0 = returnPayload .unit (1 : State) :=
  (classify_start false 0).trans rfl

private theorem unselected_ub : observed true 3 = returnPayload .unit (3 : State) :=
  (classify_start true 3).trans rfl

private theorem fault_keeps_final_state : observed true 2 = WithTop.some {Outcome.fault (3 : State)} :=
  (classify_start true 2).trans rfl

private theorem in_step_divergence :
    observed true 4 = WithTop.some ({Outcome.diverge} : Set (Outcome 1 Unit State)) :=
  (classify_start true 4).trans rfl

private theorem repeat_cycle :
    observed true 5 = WithTop.some ({Outcome.diverge} : Set (Outcome 1 Unit State)) :=
  (classify_start true 5).trans rfl

private theorem checked_refinement : ∀ s, observed false s ≤ observed true s :=
  fun s => (check_generate_iff codes primitive (body false) (body true)).mp (by decide) 0 unitPayload s

private theorem checked_reverse_failure : check (table true) (table false) = false := by decide

#print axioms observe_eval
#print axioms generate_certified
#print axioms check_generate_iff
#print axioms changing_repeat
#print axioms reaches_ub
#print axioms returns_after_repeat
#print axioms unselected_ub
#print axioms fault_keeps_final_state
#print axioms in_step_divergence
#print axioms repeat_cycle
#print axioms checked_refinement
#print axioms checked_reverse_failure

end LambdaSSAUBFiniteSyntaxRegression
