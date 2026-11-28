module

import Silmaril.SSA.Isotope.Institution.UndefinedBehaviour.LambdaSSA.Overlay.Shape.Separation.TwoRequest.Thms

namespace Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest

open Category.FiniteIteration

/-- Both endpoints repeat the first key after the left reply and use a
different key after the right reply. The right arm exposes literal UB. -/
private def endpoint (last : Tag) : Endpoint :=
  ⟨.ask, fun i => if i = 0 then ⟨.ask, fun j => .ret (if j = 0 then 0 else last)⟩
    else ⟨.other, fun _ => .ub⟩⟩

private def repeatHandler : Handler 3 :=
  prefixHandler .ask .ask (.reply 0 1) (.reply 1 2)

example : Shape.denote (endpoint 0).region repeatHandler.model 0 =
    WithTop.some {Outcome.ret (0 : Fin 2) Value.unit (2 : Fin 3)} :=
  finite_observe (endpoint 0) repeatHandler 0

example : Shape.denote (endpoint 1).region repeatHandler.model 0 =
    WithTop.some {Outcome.ret (1 : Fin 2) Value.unit (2 : Fin 3)} :=
  finite_observe (endpoint 1) repeatHandler 0

example : ¬ Shape.denote (endpoint 0).region repeatHandler.model 0 ≤
    Shape.denote (endpoint 1).region repeatHandler.model 0 := by
  rw [finite_observe, finite_observe, result_order]
  decide

private theorem one_state_executions (h : Handler 1) (s : Fin 1) :
    (endpoint 0).execute h s = (endpoint 1).execute h s := by
  have hs : s = 0 := Subsingleton.elim _ _
  subst s
  simp only [Endpoint.execute, show (endpoint 0).first = .ask from rfl,
    show (endpoint 1).first = .ask from rfl]
  cases reply : h .ask 0 with
  | fault t => rfl
  | diverge => rfl
  | reply i t =>
    have ht : t = 0 := Subsingleton.elim _ _
    subst t
    by_cases left : i = 0
    · subst i
      simp [endpoint, Row.execute, reply]
    · simp [endpoint, Row.execute, left]

/-- No one-state deterministic handler distinguishes these endpoints. It
would have to give different replies to the same key at its sole state. -/
example (h : Handler 1) (s : Fin 1) :
    Shape.denote (endpoint 0).region h.model s = Shape.denote (endpoint 1).region h.model s := by
  rw [finite_observe, finite_observe, one_state_executions]

private def selectUB : Handler 3 :=
  prefixHandler .ask .other (.reply 1 1) (.reply 0 2)

example : Shape.denote (endpoint 0).region selectUB.model 0 = ⊤ :=
  finite_observe (endpoint 0) selectUB 0

/-- A competing right reply can mask the ordered-exit difference by
reaching the UB arm. This shaped relation offers both replies at every key. -/
private abbrev bothReplies : Shape.Model.{0,0,0,0} Instr ([] : List (Silmaril.Ty Empty)) where
  raw := {
    α := Unit
    σ := Fin 3
    instr := fun _ _ s b t => (b = bitValue 0 ∨ b = bitValue 1) ∧ t = s + 1
    faults := fun _ _ _ _ => False
    prim := fun _ _ _ => False
    bound := Fin.elim0 }
  atomType := Syntax.atomType
  boundTyped i := i.elim0
  instrTyped := by
    intro f a s b t _ h
    rcases h.1 with rfl | rfl
    · exact .inl .unit
    · exact .inr .unit

example (last : Tag) : Shape.denote (endpoint last).region bothReplies 0 = ⊤ :=
  (endpoint_top _ _ _).mpr ⟨1, (1 : Fin 3), 0, (2 : Fin 3),
    ⟨.inr rfl, rfl⟩, ⟨.inl rfl, rfl⟩, rfl⟩

/-- Even when both continuations would hit UB on a successful second
reply, a differing second key is observable before either UB is reached. -/
private def toUB (second : Instr) : Endpoint :=
  ⟨.ask, fun _ => ⟨second, fun _ => .ub⟩⟩

private def failingHandler : Handler 3 :=
  prefixHandler .ask .ask (.reply 0 1) (.fault 2)

example : Shape.denote (toUB .ask).region failingHandler.model 0 =
    WithTop.some {Outcome.fault (2 : Fin 3)} :=
  finite_observe (toUB .ask) failingHandler 0

example : Shape.denote (toUB .other).region failingHandler.model 0 =
    WithTop.some {Outcome.diverge} :=
  finite_observe (toUB .other) failingHandler 0

example : ¬ Shape.denote (toUB .ask).region failingHandler.model 0 ≤
    Shape.denote (toUB .other).region failingHandler.model 0 := by
  rw [finite_observe, finite_observe, result_order]
  decide

/-- info: 'Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest.shaped_refines_iff' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms shaped_refines_iff

end Silmaril.Isotope.LambdaSSA.UB.Overlay.Shape.TwoRequest
